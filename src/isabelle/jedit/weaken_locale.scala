package isabelle.jedit
import isabelle.{GUI_Thread, Query_Operation, Editor, XML, Markup, Text, Rendering, Token, Document}
import org.gjt.sp.jedit.{View, Buffer}
import javax.swing.JOptionPane

object Move {

  sealed trait Resolved
  case class Ready(buffer: Buffer, at: Text.Offset) extends Resolved
  case class NeedsSynthesis(node: Document.Node.Name) extends Resolved // no begin/end block present
  case class NotOpen(node: Document.Node.Name) extends Resolved        // defining file not open as a buffer
  case object NotFound extends Resolved                                // maybe no markup?

  /** Which loaded node's snapshot defines `target`, and where to insert. */
  def resolve_target(target: String): Resolved = {
    // find the defining node by searching loaded snapshots
    val located: Option[(Document.Node.Name, Text.Offset)] =
      Document_Model.get_models_map().keys.iterator.flatMap { name =>
        Document_Model.get_snapshot(name)
          .flatMap(snap => Locale_Block.locale_def_offset(target, snap))
          .map(off => (name, off))
      }.nextOption()

    located match {
      case None => NotFound
      case Some((node_name, def_offset)) =>
        JEdit_Lib.jedit_buffer(node_name) match {
          case None => NotOpen(node_name)
          case Some(buffer) =>
            Isabelle.buffer_syntax(buffer)
              .flatMap(syn => Locale_Block.find_insertion(syn, buffer, def_offset)) match {
                case Some(Locale_Block.IntoExisting(_, at)) => Ready(buffer, at)
                case Some(Locale_Block.NeedsSynthesis(_))   => NeedsSynthesis(node_name)
                case None                                   => NotFound
              }
        }
    }
  }
}

object Weaken_Locale {
  val lemma_kw = Set("lemma", "theorem", "corollary", "proposition")

  /* Toggle true to always do the in place `(in L)` style, rather than trying to move lemmas**/
  val always_in_place = false

  /* Isar only allows the target spec right after the command keyword */
  private val keyword_re =
    """^\s*(?:(?:private|qualified)\s+)?(?:""" + lemma_kw.mkString("|") + ")"
  private val In_Spec = (keyword_re + """\s*\(\s*in\s+([^\s()]+)\s*\)""").r
  private val Keyword = (keyword_re + """(?![\p{L}\p{N}_'.])""").r

  case class Finding(
    name: String,
    stmt: List[(Text.Range, String)],
    range: Text.Range,                // whole lemma incl. proof (used for deletion)
    verbatim: String,                 // full original text (non-abstracted move)
    spec: Option[Text.Range] = None   // `L` in `lemma (in L)`
  ) {
    /**  these lemmas are retargeted in place and never go
        through Move.resolve_target.   */
    def in_target: Option[Text.Range] =
      spec.orElse(In_Spec.findFirstMatchIn(verbatim).map(m =>
        Text.Range(range.start + m.start(1), range.start + m.end(1))))
  }

  private def norm(s: String): String =
    s.split('.').filterNot(_ == "local").mkString(".")

  private def cartouche(s: String): String = "\u2039" + s + "\u203A"  // "‹" + s + "›"

  /** "aczel.hom_Inf" -> "hom_Inf": inside the target locale, this is pretty gross */
  private def strip_qualifier(qualifier: String, s: String): String =
    if (qualifier.isEmpty) s
    else s.replaceAll("(?<![\\p{L}\\p{N}_'.])" + java.util.regex.Pattern.quote(qualifier + "."), "")

  private def slice(f: Finding, from: Text.Offset, to: Text.Offset): String =
    f.verbatim.substring(from - f.range.start, to - f.range.start)

  /** The lemma with `subst`  spliced in and the qualifier stripped from everything not replaced */
  private def splice(f: Finding, subst: List[(Text.Range, String)], qualifier: String): String = {
    val out = new StringBuilder
    var pos = f.range.start
    for ((r, repl) <- subst.sortBy { case (r, _) => (r.start, r.stop) }) {
      out ++= strip_qualifier(qualifier, slice(f, pos, r.start))
      out ++= repl
      pos = r.stop
    }
    out ++= strip_qualifier(qualifier, slice(f, pos, f.range.stop))
    out.toString
  }

  /** The lemma with each statement token replaced by its abstraction
      and the qualifier stripped from everything else */
  def rebuild(f: Finding, abstracted: List[String], qualifier: String,
              extra: List[(Text.Range, String)] = Nil): String = {
    val stmt = f.stmt.zip(abstracted).collect {
      case ((r, src), abs) if !extra.exists { case (e, _) => e.start < r.stop && r.start < e.stop } =>
        r -> (if (abs == src) slice(f, r.start, r.stop) else cartouche(abs))
    }
    splice(f, stmt ++ extra, qualifier)
  }

  /** Range of `L` in `lemma (in L) ...`.  Isar only accepts the target spec
      directly after the command keyword. */
  private def target_spec(toks: List[(Token, Text.Offset)]): Option[Text.Range] =
    toks.filter(_._1.is_proper).dropWhile(!_._1.is_command).drop(1) match {
      case (lpar, _) :: (kw, _) :: (loc, off) :: (rpar, _) :: _
        if lpar.is_keyword("(") && kw.is_keyword("in") && rpar.is_keyword(")") =>
          Some(Text.Range(off, off + loc.source.length))
      case _ => None
    }

  /** Retarget the lemma where it stands instead of moving it */
  def retarget(f: Finding, target: String, abs: List[String], qual: String): List[Edit] = {
    val spec: Option[(Text.Range, String)] =
      f.in_target.map(_ -> target).orElse(
        Keyword.findFirstMatchIn(f.verbatim).map { m =>
          val at = f.range.start + m.end
          Text.Range(at, at) -> s" (in $target)"
        })
    spec match {
      case None => Nil
      case Some(subst) =>
        val text  = if (abs.nonEmpty) rebuild(f, abs, qual, List(subst)) else splice(f, List(subst), "")
        val old   = f.in_target.fold("")(loc => s"(in ${slice(f, loc.start, loc.stop)}) ")
        val alias = if (qual.isEmpty) "" else s"\nlemmas $old${f.name} = $qual.${f.name}"
        // same shape as the begin/end case: insert after the old text, then delete it
        List(Edit.Insert(f.range.stop, text + alias), Edit.Delete(f.range))
    }
  }

  def findings(snapshot: Document.Snapshot): List[Finding] = {
    val source = snapshot.node.source
    snapshot.node.command_iterator().collect {
      case (cmd, start) if lemma_kw(cmd.span.name) =>
        val goal_range = Text.Range(start, start + cmd.length)
        val proof_end  = CommandUtils.qed_end(snapshot, start).getOrElse(goal_range.stop)

        val toks    = cmd.span.content
        val offsets = toks.scanLeft(start)((off, t) => off + t.source.length)
        val located = toks.zip(offsets)
        val spec    = target_spec(located)
        val stmt    = located.collect {
          case (t, off) if (t.kind == Token.Kind.STRING || t.kind == Token.Kind.CARTOUCHE) &&
                           !spec.exists(_.start == off) =>   // `(in "L")` is not a statement
            (Text.Range(off, off + t.source.length), t.content)
        }

        val name = MarkupUtils.collect_markup(snapshot, Rendering.entity_elements,
          (_, m) => if (Markup.Entity.unapply(m).exists(_._1 == "fact"))
                      m.properties.collectFirst { case ("name", v) => v } else None,
          Some(goal_range)).headOption.getOrElse("")

        Finding(
          name     = norm(name),
          stmt     = stmt,
          range    = Text.Range(start, proof_end),
          verbatim = source.substring(start, proof_end),
          spec     = spec)
    }.filter(_.name.nonEmpty).toList
  }

  def format(text: String): String = "\n" + text + "\n"

  def apply(view: View): Unit = GUI_Thread.now {
    val text_area = view.getTextArea
    val doc_view  = Document_View.get(text_area).get
    val snapshot  = Document_View.rendering(doc_view).snapshot

    val found = findings(snapshot)
    if (found.isEmpty) { /* do nothing */ }
    else {
      /* Last non-end node, where full context is accessible */
      val anchor: Int =
        snapshot.node.command_iterator()
          .filter { case (c, _) => c.is_proper && c.span.name != "end" }
          .toList.lastOption
          .map { case (c, s) => s + c.length - 1 }
          .getOrElse(found.last.range.stop)

      val original_caret = text_area.getCaretPosition
      text_area.setCaretPosition(anchor)

      // name, number of statement tokens, then the tokens themselves
      val flat    = found.flatMap(f => f.name :: f.stmt.length.toString :: f.stmt.map(_._2))
      val by_name = found.map(f => f.name -> f).toMap

      // (name, target, abstracted tokens, qualifier, movable, msg)
      var results: List[(String, String, List[String], String, String, String)] = Nil

      val q = new Query_Operation(PIDE.editor, view, "weakest_locale",
                                  (st: Query_Operation.Status) =>
        if (st == Query_Operation.Status.finished) GUI_Thread.later {
          text_area.setCaretPosition(original_caret)

          val movable = results.flatMap { case (nm, target, abs, qual, mv, msg) =>
            if (mv == "true") by_name.get(nm).map(f => (target, abs, qual, msg, f)) else None
          }
          results.filter(_._5 == "true").foreach { case (nm, target, _, qual, _, msg) =>
            System.err.println(s"MOVABLE $nm -> $target [$qual]: $msg")
          }


          // A lemma is moved only into a begin/end block the target already has.  `(in L)`
          // lemmas, and lemmas whose target has no such block (NeedsSynthesis, NotOpen,
          // NotFound), are retargeted in place instead, so no target file or block
          val resolved = movable.map(_._1).distinct.map(t => t -> Move.resolve_target(t)).toMap
          def move_to(target: String, f: Finding): Option[Move.Ready] =
            if (always_in_place || f.in_target.isDefined) None
            else resolved(target) match { case r: Move.Ready => Some(r) case _ => None }

          val selected = JEditUtils.select_dialog(
            view, "Move which lemmas?", movable,
            label = { case (target, _, _, msg, f) =>
              if (move_to(target, f).isEmpty) s"$msg  [in place]" else msg })

          if (selected.nonEmpty) {
            val source_buffer = view.getBuffer
            val by_buffer = scala.collection.mutable.Map[Buffer, List[Edit]]().withDefaultValue(Nil)

            val skipped = selected.flatMap { case (target, abs, qual, _, f) =>
              move_to(target, f) match {
                case Some(Move.Ready(tgt_buffer, at)) =>
                  val text = if (abs.nonEmpty) rebuild(f, abs, qual) else f.verbatim
                  by_buffer(source_buffer) = Edit.Delete(f.range) :: by_buffer(source_buffer)

                  if (qual.nonEmpty)
                    by_buffer(source_buffer) =
                      Edit.Insert(f.range.stop, s"lemmas ${f.name} = $qual.${f.name}") ::
                        by_buffer(source_buffer)
                  by_buffer(tgt_buffer) = Edit.Insert(at, format(text)) :: by_buffer(tgt_buffer)
                  None
                case None =>
                  retarget(f, target, abs, qual) match {
                    case Nil => Some(s"${f.name} → $target: ${resolved(target)}")
                    case edits =>
                      by_buffer(source_buffer) = edits ::: by_buffer(source_buffer)
                      None
                  }
              }
            }

            by_buffer.foreach { case (buf, es) => Edit.apply_to_buffer(buf, es) }
            if (skipped.nonEmpty)
              JEditUtils.select_dialog(view, "Skipped", skipped, label = (s: String) => s)
          }
        }, (out: Editor.Output) => {
          results = out.messages.collectFirst {
            case XML.Elem(_, List(XML.Elem(Markup("weakest_locale", _), body))) => body
          }.getOrElse(Nil).collect {
            case XML.Elem(Markup("finding", props), fbody) =>
              def p(k: String) = props.collectFirst { case (`k`, v) => v }.getOrElse("")
              val n = p("nabs").toIntOption.getOrElse(0)
              (p("name"), p("target"), (0 until n).map(i => p("abs" + i)).toList,
               p("qualifier"), p("movable"), XML.content(fbody))
          }
          System.err.println(s"PARSED results n=${results.length}: ${results.take(3)}")
        })

      System.err.println(s"FLAT n=${flat.length}: ${flat.take(6)}")
      q.activate(); q.apply_query(flat)
    }
  }
}
