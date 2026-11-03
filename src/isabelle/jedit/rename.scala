package isabelle.jedit

import isabelle.{Command, Document, File, GUI_Thread, Markup, Path, Rendering, Symbol, Text, Value}
import javax.swing.JOptionPane
import org.gjt.sp.jedit.{View, jEdit}
import org.gjt.sp.jedit.io.VFSManager
import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.{Await, Promise}
import scala.concurrent.duration.Duration
import scala.util.Try


/* Rename a constant, fact, locale, class or type across the session, using the PIDE
   markup of the headless proc.

   Not handled: names in ML strings and comments, class instantiations (foo_nat),
   prefix-generated names (case_foo, Rep_foo), quoted name tokens, and locale
   parameters: each locale context re-fixes them without a position
   (Locale.activate_all uses Binding.name), so only the uses in one context are found. */
object Rename {


  // node and start offset of the bound name
  private sealed case class Def_Key(node: String, offset: Int)

  private sealed case class Occ(
    range: Text.Range,
    kind: String,
    name: String,
    serial: Option[Long],
    def_key: Option[Def_Key]
  ) {
    def base: String = MarkupUtils.short_name(name)
  }

  // def_id -> start of that command
  private final class Def_Resolver {
    private val cache = mutable.Map.empty[Long, Option[(String, Int, Command)]]

    def apply(snapshot: Document.Snapshot, id: Long, symbol_offset: Int): Option[Def_Key] =
      cache.getOrElseUpdate(id,
                            for ((node, cmd) <- snapshot.find_command(id); start <- node.command_start(cmd))
                            yield (cmd.node_name.node, start, cmd)
      ).map { case (node, start, cmd) => Def_Key(node, start + cmd.chunk.decode(symbol_offset)) }
  }

  // Def markup is keyed by its own range (PIDE strips positions from markup)).
  // Ref markup is keyed by def_id/def_offset, which point at the binding.
  private def entity_occs(
    snapshot: Document.Snapshot,
    resolver: Def_Resolver,
    range: Option[Text.Range] = None
  ): List[Occ] =
    MarkupUtils.collect_markup[Occ](snapshot, Rendering.entity_elements, { (r, m) =>
      def get(key: String): Option[String] = m.properties.collectFirst { case (k, v) if k == key => v }
      val def_serial = get("def").flatMap(Value.Long.unapply)
      val def_key =
        if (def_serial.isDefined) Some(Def_Key(snapshot.node_name.node, r.start))
        else
          for {
            id <- get("def_id").flatMap(Value.Long.unapply)
            offset <- get("def_offset").flatMap(Value.Int.unapply)
            key <- resolver(snapshot, id, offset)
          } yield key
      if (m.name != Markup.ENTITY) None
      else Some(Occ(r, get("kind").getOrElse(""), Symbol.encode(get("name").getOrElse("")),
        def_serial orElse get("ref").flatMap(Value.Long.unapply), def_key))
    }, range)


  /* kinds and names */

  // kinds that can stand for the same binding (i.e., the same entity with different kind)
  private val alias_group: Map[String, Set[String]] = Map(
    "constant" -> Set("constant", "fixed"),
    "fixed" -> Set("constant", "fixed"),
    "fact" -> Set("fact"),
    "type_name" -> Set("type_name"),
    "locale" -> Set("locale", "class"),
    "class" -> Set("locale", "class"))

  // suffixes of generated names. facts have no generated names
  private val generated_suffixes: Map[String, List[String]] = Map(
    "constant" -> List("_def", "_graph", "_rel", "_dom", "_sumC"),
    "fixed" -> List("_def", "_graph", "_rel", "_dom", "_sumC"),
    "locale" -> List("_def", "_axioms", "_axioms_def"),
    "class" -> List("_def", "_axioms", "_axioms_def"),
    "type_name" -> Nil)

  private def spells(text: String, short: String): Option[Int] =
    if (text == short) Some(0)
    else if (text.endsWith("." + short)) Some(text.length - short.length)
    else None

  private def derived_offset(
    kind: String, family: String, short: String, name: String, text: String
  ): Option[Int] =
    generated_suffixes.get(kind).flatMap { suffixes =>
      val f = family.split('.').toList
      val n = name.split('.').toList
      val t = text.split('.').toList
      val depth = f.length - 1
      val i = depth - (n.length - t.length)  // the family's component, as an index into t
      def generated(c: String): Boolean = c == short || suffixes.exists(s => c == short + s)
      if (name == family || n.length <= depth || n.take(depth) != f.take(depth) ||
          !generated(n(depth)) || t.length > n.length || t != n.takeRight(t.length) || i < 0) None
      else Some(t.take(i).map(_.length + 1).sum)
    }

  private def is_identifier(s: String): Boolean = {
    val syms = Symbol.explode(Symbol.encode(s))
    syms.nonEmpty && Symbol.is_letter(syms.head) &&
      syms.forall(sym => Symbol.is_letdig(sym) || sym == Symbol.sub)
  }


  /* the entity under the caret */

  // Serials differ between the editor's ML process and the headless one,
  // so the entity is carried over by kind, name and location.
  private sealed case class Seed(kind: String, name: String, file: String, line: Int)

  private def seed_at_caret(view: View): Option[Seed] = {
    val text_area = view.getTextArea
    for {
      doc_view <- Document_View.get(text_area)
      snapshot = Document_View.rendering(doc_view).snapshot
      caret = JEdit_Lib.caret_range(text_area)
      source = snapshot.node.source
      occ <- entity_occs(snapshot, new Def_Resolver, Some(caret))
        .filter(o => alias_group.contains(o.kind) && o.range.contains(caret.start))
      .sortBy(o => (
                spells(Symbol.encode(source.substring(o.range.start, o.range.stop)), o.base).isEmpty,
                o.range.length,
                o.kind == "fixed"))
      .headOption
    } yield Seed(occ.kind, occ.name, view.getBuffer.getPath, view.getBuffer.getLineOfOffset(occ.range.start))
  }

  private sealed case class Node(name: Document.Node.Name, snapshot: Document.Snapshot, occs: List[Occ]) {
    def source: String = snapshot.node.source
    def text(r: Text.Range): String = source.substring(r.start, r.stop)
    def line_of(offset: Int): Int = source.substring(0, offset).count(_ == '\n')
    def is_file(file: String): Boolean =
      Try(Path.explode(name.node).file.getCanonicalFile == new java.io.File(file).getCanonicalFile)
        .getOrElse(false)
  }

  // the caret's occurrence, plus (for global names) every occurrence of that name
  private def seed_serials(seed: Seed, nodes: List[Node]): Set[Long] = {
    def same(o: Occ): Boolean = o.kind == seed.kind && o.name == seed.name
    val at_caret =
      for (n <- nodes if n.is_file(seed.file); o <- n.occs if same(o) && n.line_of(o.range.start) == seed.line)
        yield o
    val global =
      if (seed.kind == "fixed" || seed.name.startsWith("local.")) Nil
      else nodes.flatMap(_.occs).filter(same)
    (at_caret ++ global).flatMap(_.serial).toSet
  }

  // add entities bound at the same position, with the same base name
  @tailrec private def close_aliases(kind: String, short: String, serials: Set[Long], all: List[Occ]): Set[Long] = {
    val keys = all.filter(_.serial.exists(serials)).flatMap(_.def_key).toSet
    val more = all.filter(o => alias_group(kind)(o.kind) && o.base == short && o.def_key.exists(keys))
      .flatMap(_.serial).toSet -- serials
    if (more.isEmpty) serials else close_aliases(kind, short, serials ++ more, all)
  }


  /* planning */

  private sealed case class Site(node: Document.Node.Name, range: Text.Range, label: String)

  private sealed case class Plan(
    kind: String,
    name: String,
    short: String,
    nodes: List[Node],
    sites: List[Site],
    unchanged: Int,   // occurrences whose text is not the name, e.g. notation
    errors_before: Map[Document.Node.Name, Int]
  )

  private def error_count(snapshot: Document.Snapshot): Int =
    MarkupUtils.find_markup(snapshot, Rendering.error_elements, _ => true).length

  private def make_plan(seed: Seed, current_file: String, progress: isabelle.Progress): Option[Plan] = {
    Headless_Handler.ensure_running(current_file, progress)
    val resolver = new Def_Resolver
    val nodes =
      for (name <- Headless_Handler.nodes; snapshot <- Headless_Handler.snapshot(name))
        yield Node(name, snapshot, entity_occs(snapshot, resolver))
    val all = nodes.flatMap(_.occs)
    val short = MarkupUtils.short_name(seed.name)
    val seeds = seed_serials(seed, nodes)

    if (seeds.isEmpty) None
    else {
      val serials = close_aliases(seed.kind, short, seeds, all)
      val family = all.filter(o => o.serial.exists(serials) && o.kind != "fixed").map(_.name).distinct
      var unchanged = 0

      def site(n: Node, r: Text.Range, offset: Int, note: String): Site = {
        val start = r.start + offset
        Site(n.name, Text.Range(start, start + short.length),
          s"${n.name.theory.stripPrefix("Draft.")}:${n.line_of(start) + 1}   ${n.text(r)}$note")
      }

      val sites = nodes.flatMap { n =>
        val direct = n.occs.filter(_.serial.exists(serials)).map(_.range).distinct.flatMap { r =>
          val offset = spells(n.text(r), short)
          if (offset.isEmpty) unchanged += 1
          offset.map(site(n, r, _, ""))
        }
        val generated = n.occs.filterNot(_.serial.exists(serials)).flatMap { o =>
          family.iterator.flatMap(f => derived_offset(seed.kind, f, short, o.name, n.text(o.range)))
            .nextOption().map(site(n, o.range, _, "   (generated name)"))
        }
        (direct ++ generated).distinctBy(_.range)
      }

      Some(Plan(seed.kind, seed.name, short, nodes, sites, unchanged,
        nodes.map(n => n.name -> error_count(n.snapshot)).toMap))
    }
  }


  /* UI */

  private def message(view: View, text: String): Unit =
    JOptionPane.showMessageDialog(view, text, "Rename", JOptionPane.INFORMATION_MESSAGE)

  // run `body` on a worker thread behind the modal progress dialog; None if cancelled
  private def with_progress[A](view: View)(body: isabelle.Progress => A): Option[Either[Throwable, A]] = {
    val (dialog, label) = JEditUtils.progress_dialog(view)
    val progress = JEditUtils.theory_progress(label)
    val result = Promise[A]()
    dialog.addWindowListener(new java.awt.event.WindowAdapter {
      override def windowClosing(e: java.awt.event.WindowEvent): Unit = {
        progress.stop()
        Headless_Handler.cancel()
        label.setText("Cancelling\u2026")
      }
    })
    new Thread(() => {
      try { result.success(body(progress)); () }
      catch { case e: Throwable => result.failure(e); () }
      finally { GUI_Thread.later { dialog.dispose() } }
    }, "isabelle-rename").start()
    dialog.setVisible(true)
    if (progress.stopped) None
    else Some(Try(Await.result(result.future, Duration.Inf)).toEither)
  }

  def apply(view: View): Unit = GUI_Thread.now {
    seed_at_caret(view) match {
      case None => message(view, "No constant, fact, locale, class or type at the caret.")
      case Some(seed) =>
        jEdit.getBuffers.foreach(buf => if (buf.isDirty) buf.save(view, null))
        VFSManager.waitForRequests()
        val current_file = view.getBuffer.getPath
            with_progress(view)(make_plan(seed, current_file, _)) match {
          case Some(Right(Some(plan))) if plan.sites.isEmpty =>
            message(view, s"Found ${plan.kind} ${plan.name}, but no occurrence spells its name.")
          case Some(Right(Some(plan))) => prompt_and_apply(view, plan)
          case Some(Right(None)) => message(view, s"${seed.name} was not found in the checked session.")
          case Some(Left(exn)) => message(view, "Rename failed: " + exn.getMessage)
          case None =>  // cancelled
        }
    }
  }

  private def prompt_and_apply(view: View, plan: Plan): Unit = {
    val note =
      if (plan.unchanged == 0) ""
      else s"\n(${plan.unchanged} occurrence(s) whose text is not the name, e.g. notation, are left unchanged)"
    val input = Option(JOptionPane.showInputDialog(view,
      s"Rename ${plan.kind} ${plan.name}: ${plan.sites.length} occurrence(s)$note\n\nNew name:",
      "Rename", JOptionPane.QUESTION_MESSAGE, null, null, plan.short)).map(_.toString.trim)

    input match {
      case Some(new_name) if new_name.nonEmpty && Symbol.encode(new_name) != plan.short =>
        if (!is_identifier(new_name)) message(view, s"'$new_name' is not an identifier.")
        else {
          val chosen = JEditUtils.select_dialog(view, s"Rename ${plan.short} \u2192 $new_name",
            plan.sites, (s: Site) => s.label, preselected = true)
          if (chosen.nonEmpty) apply_and_verify(view, plan, chosen, Symbol.encode(new_name))
        }
      case _ =>
    }
  }

  private def reload_buffers(view: View, paths: List[Path]): Unit =
    for (path <- paths; buffer <- Option(jEdit.getBuffer(path.file.getCanonicalPath)))
      buffer.reload(view)

  private def apply_and_verify(view: View, plan: Plan, sites: List[Site], replacement: String): Unit = {
    val written = mutable.ListBuffer.empty[(Path, String)]
    val skipped = mutable.ListBuffer.empty[String]

    // site ranges are offsets into the text the headless session checked
    for ((name, node_sites) <- sites.groupBy(_.node); node <- plan.nodes.find(_.name == name)) {
      val path = Path.explode(name.node)
      val text = File.read(path)
      if (text != node.source) skipped += name.theory
      else {
        File.write(path, Edit.apply_to_text(text, node_sites.map(s => Edit.Replace(s.range, replacement))))
        written += (path -> text)
      }
    }
    reload_buffers(view, written.map(_._1).toList)
    if (skipped.nonEmpty)
      message(view, "Skipped, file differs from the checked text: " + skipped.mkString(", "))

    if (written.nonEmpty) {
      val recheck = with_progress(view) { progress =>
        Headless_Handler.refresh(progress)
        Headless_Handler.nodes.flatMap(n => Headless_Handler.snapshot(n).map(s => n -> error_count(s)))
      }
      recheck match {
        case Some(Right(after)) =>
          val worse = after.collect { case (n, k) if k > plan.errors_before.getOrElse(n, 0) => n.theory }
          if (worse.nonEmpty &&
              JOptionPane.showConfirmDialog(view,
                "New errors in: " + worse.mkString(", ") + "\nRevert the rename?",
                "Rename", JOptionPane.YES_NO_OPTION) == JOptionPane.YES_OPTION) {
            written.foreach { case (path, text) => File.write(path, text) }
            reload_buffers(view, written.map(_._1).toList)
          }
        case _ => message(view, "The rename was applied but not re-checked.")
      }
    }
  }
}
