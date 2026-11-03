package isabelle.jedit

import isabelle.{Document, Rendering, GUI_Thread, Command, Text, Query_Operation, XML,
  Editor, Markup, Properties, Symbol, Value}
import org.gjt.sp.jedit.View
import javax.swing.JOptionPane

object Promote_Have {

  /* Results from prover*/

  sealed trait LiftCheck
  case class Liftable(info: LiftInfo) extends LiftCheck
  case class Rejected(
    hyps: List[String]                    = Nil,
    fixed_in_prop: List[(String, String)] = Nil,
    local_deps: List[String]              = Nil,
    other: Option[String]                 = None
  ) extends LiftCheck

  // What check_liftable reports about a finished have block
  case class LiftInfo(
    fixes: List[(String, String)],        // local fixed vars: (name, type)
    deps: List[(String, List[String])],   // referenced local facts: (name, statements)
    unresolved: List[String],             // references that didn't resolve
    hyps: List[(String, List[String])]    // open hyps: (statement, names in context)
  )

  // What chained_facts reports about a then/from/with directly before the block
  case class ChainInfo(
    globals: List[String],                // global facts
    fixes: List[(String, String)],
    usable: List[(String, List[String])], // chained facts the target provides
    facts: List[(String, List[String])]   // chained local facts: (statement, names in context)
  )

  // A premise of the lifted lemma: its name there ("" for an unnamed group), its
  // statements, and how a use site in the original proof refers to the same facts
  case class Premise(name: String, props: List[String], ref: String)

  // Where the lifted lemma goes, and in which target it is stated
  case class Placement(
    offset: Text.Offset,                  // insertion point
    before_goal: Boolean,                 // just before the enclosing goal, or after `begin`
    in_clause: Option[String],            // the enclosing goal's `(in loc)`, repeated
    target: Option[String]                // the locale or class the lemma is stated in
  )

  private val chain_keywords = Set("then", "from", "with")
  private val reserved_refs  = Set("this", "calculation", "that")


  def apply(view: View): Unit = {
    GUI_Thread.now {
      val text_area = view.getTextArea()
      val doc_view  = Document_View.get(text_area).get
      val snapshot  = Document_View.rendering(doc_view).snapshot
      val caret     = text_area.getCaretPosition

      snapshot.node.command_iterator(caret).nextOption() match {
        case Some((cmd, cmd_start)) if cmd.span.name == "have" =>
          have_block_range(snapshot.node, cmd_start) match {
            case Some(range) =>
              check_liftability_and_promote(view, snapshot, cmd, range)
            case None =>
              JOptionPane.showMessageDialog(
                view,
                "Could not determine the range of the 'have' block.",
                "Promote_Have",
                JOptionPane.WARNING_MESSAGE
              )
          }
        case _ =>
          JOptionPane.showMessageDialog(
            view,
            "No 'have' command found under caret.",
            "Promote_Have",
            JOptionPane.INFORMATION_MESSAGE
          )
      }
    }
  }


  def check_liftability_and_promote(
    view: View, snapshot: Document.Snapshot,
    have_cmd: Command, range: Text.Range
  ): Unit = {
    val user_caret = view.getTextArea.getCaretPosition
    val block = HaveNode(range, view.getBuffer.getText(range.start, range.length), have_cmd)
    val own_name = block.parse_head._1
    val refs = collect_external_local_refs(snapshot, range)
    val place = placement(snapshot, range.start)
    val target_arg = place.target.getOrElse("")

    val early_rejection: Option[Rejected] =
      check_chaining_supported(snapshot, range)
        .orElse(refs.find(reserved_refs).map(r =>
          Rejected(other = Some(s"the block refers to '$r'"))))
        .orElse(own_name.filter(refs.contains).map(n =>
          Rejected(other = Some(
            s"the block refers to an earlier fact '$n', which its own name shadows"))))

    early_rejection match {
      case Some(r) => show_rejection(view, r)
      case None =>
        run_query(view, "check_liftable", range.stop - 1, target_arg :: refs, user_caret)(
          parse_lift_response) {
          case r: Rejected => show_rejection(view, r)
          case Liftable(info) if info.unresolved.nonEmpty =>
            show_rejection(view, Rejected(local_deps = info.unresolved,
              other = Some("could not resolve some local facts the block uses")))
          case Liftable(info) =>
            chain_command_before(snapshot, range.start) match {
              case None =>
                promote(view, snapshot, block, refs, info, None, place)
              case Some((chain_cmd, chain_start)) =>
                val chain_refs = collect_fact_refs(snapshot,
                  Text.Range(chain_start, chain_start + chain_cmd.length))
                val as_written = chain_refs.toMap
                run_query(view, "chained_facts", chain_start + 1,
                    target_arg :: chain_refs.map(_._1), user_caret)(parse_chain_response) {
                  case Left(r) => show_rejection(view, r)
                  case Right(chain) =>
                    // use global facts by the name written in the source, not their full
                    // name: inside a locale the two can denote different theorems
                    val chain1 =
                      chain.copy(globals = chain.globals.map(g => as_written.getOrElse(g, g)))
                    promote(view, snapshot, block, refs, info,
                      Some((chain_start, chain1)), place)
                }
            }
        }
    }
  }


  def promote(
    view: View, snapshot: Document.Snapshot, block: HaveNode,
    refs: List[String], info: LiftInfo,
    chain: Option[(Text.Offset, ChainInfo)],
    place: Placement
  ): Unit = {
    val (name_opt, prop_opt) = block.parse_head
    val name = prompt_lemma_name(view, name_opt) match {
      case Some(n) => n
      case None    => return  // cancelled
    }

    val shows = prop_opt.getOrElse(
      throw new IllegalStateException("no prop in have head"))

    val (premises, chained_names) =
      build_premises(info, chain.map(_._2), refs.toSet + name)
    val fixes =
      (info.fixes ::: chain.toList.flatMap(_._2.fixes)).distinctBy(_._1)
    val chain_using =
      chain.toList.flatMap { case (_, c) =>
        c.globals ::: c.usable.map { case (prop, names) =>
          names.headOption.getOrElse(Symbol.cartouche_decoded(prop))
        }
      } ::: chained_names

    val proof_tail = block.source.substring(block.head_range.length).trim
    val lemma_text =
      to_lemma_text(name, place.in_clause, fixes, premises, shows, chain_using, proof_tail)

    // how each premise is supplied at the old fact's use sites
    val premise_refs = premises.map(_.ref)
    val full_source = snapshot.node.source

    val target_serial =
      MarkupUtils.find_fact_defs(snapshot, block.head_range).headOption.map(_._1)

    val ref_rewrites: List[Edit] =
      target_serial.toList.flatMap { serial =>
        MarkupUtils.find_fact_refs(snapshot, Text.Range(0, full_source.length))
          .collect { case (s, r) if s == serial && !block.range.contains(r) => r }
          .map(r => rewrite_reference(full_source, r, name, premise_refs))
      }

    val chained_rewrites: List[Edit] =
      find_chained_ref_after(snapshot, block.range.stop)
        .toList
        .flatMap(p => rewrite_chained_reference(full_source, p._1, p._2, name, premise_refs))

    // a then/from/with before the block only fed the block, so it goes too
    val chain_deletion: List[Edit] =
      chain.toList.map { case (start, _) => Edit.Delete(Text.Range(start, block.range.start)) }

    val insertion =
      if (place.before_goal) Edit.Insert(place.offset, lemma_text + "\n")
      else Edit.Insert(place.offset, "\n\n" + lemma_text)

    val edits = ref_rewrites ::: chained_rewrites ::: chain_deletion ::: List(
      insertion,
      Edit.Delete(block.range)
    )
    Edit.apply_to_buffer(view.getBuffer, edits)
  }


  /* Placement */

  // Insert the lifted lemma just before the top-level goal whose proof contains the
  // block: everything the block could see at theory level is declared before that point,
  // and the lemma lands inside the same context/locale block, if any.
  // Falls back to just after the theory's `begin` if there is no enclosing goal.
  def placement(snapshot: Document.Snapshot, block_start: Text.Offset): Placement = {
    var open_blocks: List[Option[String]] = Nil     // innermost first
    var goal: Option[(Command, Text.Offset)] = None

    for {
      (cmd, start) <- snapshot.node.command_iterator(0).takeWhile(_._2 < block_start)
      if cmd.is_proper
    } {
      val name = cmd.span.name
      if (cmd.span.is_keyword_kind(_.startsWith("thy_goal"))) goal = Some((cmd, start))
      if (name == "end") open_blocks = open_blocks.drop(1)
      else if (name != "theory" &&
               cmd.span.content.exists(t => t.is_keyword && t.source == "begin"))
        open_blocks = block_target(cmd) :: open_blocks
    }

    goal match {
      case Some((cmd, start)) =>
        val in_clause = in_target(cmd)
        Placement(start, before_goal = true, in_clause,
          in_clause.orElse(open_blocks.flatten.headOption))
      case None =>
        Placement(MarkupUtils.offset_after_begin(snapshot).get, before_goal = false,
          None, None)
    }
  }

  // The `(in loc)` of a goal `lemma (in loc) foo: ...`
  def in_target(cmd: Command): Option[String] =
    cmd.span.content.filter(_.is_proper).map(_.source) match {
      case _ :: "(" :: "in" :: loc :: ")" :: _ => Some(loc)
      case _ => None
    }

  // The locale or class a block is in, if named
  private def block_target(cmd: Command): Option[String] =
    if (Set("context", "locale", "class").contains(cmd.span.name))
      cmd.span.content.filter(_.is_proper).drop(1).headOption
        .filter(_.is_name).map(_.source)
    else None


  /* Premises */

  // Premises of the lifted lemma, and the names of those to be chained into its proof
  def build_premises(
    info: LiftInfo, chain: Option[ChainInfo], taken: Set[String]
  ): (List[Premise], List[String]) = {
    var used = taken ++ info.deps.map(_._1)

    def fresh(): String = {
      val n = Iterator.from(1).map(i => s"h$i").find(n => !used(n)).get
      used += n
      n
    }
    // reuse a name the fact already has in context, if it is free, otherwise make one
    def lemma_name(names: List[String]): String =
      names.find(n => !used(n)) match {
        case Some(n) => used += n; n
        case None    => fresh()
      }
    def use_site_ref(prop: String, names: List[String]): String =
      names.headOption.getOrElse(Symbol.cartouche_decoded(prop))

    // referenced local facts. the outer lemma's assms go first, unnamed, so that
    // assms(i) in the copied proof still means what it meant before
    val (assms, other_deps) = info.deps.partition(_._1 == "assms")
    var premises: List[Premise] =
      assms.map { case (_, props) => Premise("", props, "assms") } :::
      other_deps.map { case (n, props) => Premise(n, props, n) }

    // chained facts: reuse a named premise with the same statement, otherwise add one
    val chained_names: List[String] =
      chain.toList.flatMap(_.facts).map { case (prop, names) =>
        premises.find(p => p.name.nonEmpty && p.props == List(prop)) match {
          case Some(p) => p.name
          case None =>
            val p = Premise(lemma_name(names), List(prop), use_site_ref(prop, names))
            premises = premises :+ p
            p.name
        }
      }

    // hypotheses of the result that no premise states yet
    for ((prop, names) <- info.hyps if !premises.exists(_.props.contains(prop))) {
      premises = premises :+
        Premise(lemma_name(names), List(prop), use_site_ref(prop, names))
    }

    (premises, chained_names)
  }


  /* Prover queries */

  // Run a query operation on the command at `offset`, and hand the first parseable
  // result to `on_result`. The caret is moved for the query and restored afterwards.
  private def run_query[A](
    view: View, operation: String, offset: Int, args: List[String], restore_caret: Int
  )(parse: Editor.Output => Option[A])(on_result: A => Unit): Unit = {
    val text_area = view.getTextArea
    var delivered = false
    lazy val query: Query_Operation =
      new Query_Operation(PIDE.editor, view, operation,
        (status: Query_Operation.Status) =>
          if (status == Query_Operation.Status.finished)
            GUI_Thread.later { text_area.setCaretPosition(restore_caret) },
        (output: Editor.Output) =>
          GUI_Thread.later {
            if (!delivered) parse(output).foreach { result =>
              delivered = true
              text_area.setCaretPosition(restore_caret)
              query.deactivate()
              on_result(result)
            }
          })
    text_area.setCaretPosition(offset)
    query.activate()
    query.apply_query(args)
  }

  private def child(body: XML.Body, tag: String): XML.Body =
    body.collectFirst { case XML.Elem(Markup(name, _), b) if name == tag => b }
      .getOrElse(Nil)

  private def children(body: XML.Body, tag: String): List[XML.Body] =
    body.collect { case XML.Elem(Markup(name, _), b) if name == tag => b }

  private def texts(body: XML.Body, tag: String): List[String] =
    children(body, tag).map(b => XML.content(b))

  private def parse_fixes(body: XML.Body): List[(String, String)] =
    children(child(body, "fixes"), "var").map(v =>
      (texts(v, "name").headOption.getOrElse(""), texts(v, "typ").headOption.getOrElse("_")))

  private def parse_stmts(body: XML.Body, tag: String): List[(String, List[String])] =
    children(body, tag).map(s => (texts(s, "prop").headOption.getOrElse(""), texts(s, "name")))

  def parse_lift_response(output: Editor.Output): Option[LiftCheck] =
    output.messages.collectFirst {
      case XML.Elem(_, List(XML.Elem(Markup("liftable_check", _), body))) =>
        Liftable(LiftInfo(
          fixes = parse_fixes(body),
          deps = children(child(body, "deps"), "dep").map(d =>
            (texts(d, "name").headOption.getOrElse(""), texts(d, "prop"))),
          unresolved = texts(child(body, "unresolved"), "name"),
          hyps = parse_stmts(child(body, "hyps"), "hyp")))
      case XML.Elem(_, List(XML.Elem(Markup("liftable_check_error", _), msg))) =>
        Rejected(other = Some("ML error: " + XML.content(msg)))
      case XML.Elem(_, List(XML.Elem(Markup("liftable_check_not_in_proof", _), _))) =>
        Rejected(other = Some("not in a proof state"))
    }

  def parse_chain_response(output: Editor.Output): Option[Either[Rejected, ChainInfo]] =
    output.messages.collectFirst {
      case XML.Elem(_, List(XML.Elem(Markup("chained_facts", _), body))) =>
        Right(ChainInfo(
          globals = texts(child(body, "globals"), "name"),
          fixes = parse_fixes(body),
          usable = parse_stmts(child(body, "usable"), "fact"),
          facts = parse_stmts(child(body, "facts"), "fact")))
      case XML.Elem(_, List(XML.Elem(Markup("chained_facts_error", _), msg))) =>
        Left(Rejected(other = Some("ML error: " + XML.content(msg))))
      case XML.Elem(_, List(XML.Elem(Markup("chained_facts_not_in_proof", _), _))) =>
        Left(Rejected(other = Some("the chaining command is not in a proof state")))
    }


  /* Markup */

  // Local facts referred to in `range`, excluding those defined inside it (they move
  // with the block); names without the "local." prefix
  def collect_external_local_refs(
    snapshot: Document.Snapshot,
    range: Text.Range
  ): List[String] = {
    val defined_inside: Set[Long] =
      MarkupUtils.find_fact_defs(snapshot, range).map(_._1).toSet
    snapshot
      .cumulate[List[String]](
        range,
        Nil,
        Rendering.entity_elements,
        _ => {
          case (acc, Text.Info(_, XML.Elem(markup, _))) =>
            val ref_serial =
              Properties.get(markup.properties, "ref").flatMap(Value.Long.unapply)
            Markup.Entity.unapply(markup) match {
              case Some(("fact", name))
                  if name.startsWith("local.") &&
                    ref_serial.exists(s => !defined_inside.contains(s)) =>
                Some(name.stripPrefix("local.") :: acc)
              case _ => None
            }
        }
      )
      .flatMap(x => x.info)
      .distinct
  }

  // Facts referred to in `range`, as (name for the prover, text as written): local ones
  // without "local.", global ones by full name
  def collect_fact_refs(
    snapshot: Document.Snapshot,
    range: Text.Range
  ): List[(String, String)] = {
    val source = snapshot.node.source
    snapshot
      .cumulate[List[(String, String)]](
        range,
        Nil,
        Rendering.entity_elements,
        _ => {
          case (acc, Text.Info(r, XML.Elem(markup, _))) =>
            val is_reference = markup.properties.exists(_._1 == "ref")
            Markup.Entity.unapply(markup) match {
              case Some(("fact", name)) if is_reference =>
                Some((name.stripPrefix("local."), source.substring(r.start, r.stop)) :: acc)
              case _ => None
            }
        }
      )
      .flatMap(x => x.info)
      .distinct
  }


  /* Blocks and commands */

  def have_block_range(node: Document.Node, have_start: Text.Offset): Option[Text.Range] = {
    val it = node.command_iterator(have_start)
      .filter(_._1.is_proper)
      .drop(1)                                          // skip the `have`
      .dropWhile { case (c, _) => is_proof_modifier(c) }

    it.nextOption().flatMap { case (first_cmd, first_start) =>
      val first_end = first_start + first_cmd.length

      if (is_terminal_method(first_cmd))
        Some(Text.Range(have_start, first_end))
      else if (is_proof_open(first_cmd)) {
        var depth = 1
        var last_end = first_end
        while (depth > 0 && it.hasNext) {
          val (c, s) = it.next()
          if (is_proof_open(c)) depth += 1
          else if (is_proof_close(c)) depth -= 1
          last_end = s + c.length
        }
        if (depth == 0) Some(Text.Range(have_start, last_end)) else None
      }
      else None
    }
  }

  def collect_sibling_haves(
    snapshot: Document.Snapshot,
    scope: Text.Range
  ): List[HaveNode] = {
    CommandUtils.find_commands(snapshot, scope) { (cmd, start) =>
      if (cmd.span.name != "have") None
      else have_block_range(snapshot.node, start).map { range =>
        val source = snapshot.node.source.substring(range.start, range.stop)
        HaveNode(range, source, cmd)
      }
    }
  }

  def chain_command_before(
    snapshot: Document.Snapshot, offset: Text.Offset
  ): Option[(Command, Text.Offset)] =
    proper_command_before(snapshot, offset).filter { case (cmd, _) =>
      chain_keywords.contains(cmd.span.name)
    }

  def proper_command_before(
    snapshot: Document.Snapshot, offset: Text.Offset
  ): Option[(Command, Text.Offset)] = {
    var last: Option[(Command, Text.Offset)] = None
    val it = snapshot.node.command_iterator(0)
    while (it.hasNext) {
      val (cmd, start) = it.next()
      if (start >= offset) return last
      if (cmd.is_proper) last = Some((cmd, start))
    }
    last
  }

  def check_chaining_supported(
    snapshot: Document.Snapshot,
    range: Text.Range
  ): Option[Rejected] = {
    val calc_keywords = Set("also", "finally", "moreover", "ultimately")
    val before = proper_command_before(snapshot, range.start).map(_._1.span.name)
    val after  = CommandUtils.proper_commands(
      snapshot, Text.Range(range.stop, snapshot.node.source.length))
      .nextOption().map(_._1.span.name)

    val unsupported_before = before.filter(calc_keywords.contains)
    val unsupported_after  = after.filter(calc_keywords.contains)

    (unsupported_before, unsupported_after) match {
      case (None, None) => None
      case (b, a) =>
        val parts = b.map(k => s"preceded by '$k'").toList ++
        a.map(k => s"followed by '$k'").toList
        Some(Rejected(other = Some(
          s"calculation chaining not supported (${parts.mkString(", ")})")))
    }
  }

  /* Predicates */
  def is_proof_open(cmd: Command):  Boolean = cmd.span.is_keyword_kind(_ == "prf_block")
  def is_proof_close(cmd: Command): Boolean = cmd.span.is_keyword_kind(_ == "qed_block")
  def is_terminal_method(cmd: Command): Boolean = cmd.span.is_keyword_kind(_ == "qed")
  def is_proof_modifier(cmd: Command):  Boolean =
    cmd.span.is_keyword_kind(k => k == "prf_decl" || k == "prf_chain")


  /* Text generation and rewriting */

  def to_lemma_text(
    name: String,
    in_clause: Option[String],         // `(in loc)` to repeat, if any
    fixes: List[(String, String)],     // (name, type)
    premises: List[Premise],
    shows: String,
    chain_using: List[String],         // facts the original block had chained into it
    proof: String
  ): String = {
    val sb = new StringBuilder
    sb ++= in_clause.map(loc => s"lemma (in $loc) $name:\n").getOrElse(s"lemma $name:\n")

    for (((n, t), i) <- fixes.zipWithIndex)
      sb ++= (if (i == 0) "  fixes " else "      and ") + s"$n :: \"$t\"\n"

    for ((p, i) <- premises.zipWithIndex) {
      val binding = if (p.name.isEmpty) "" else s"${p.name}: "
      val props = p.props.map(Symbol.cartouche_decoded).mkString(" ")
      sb ++= (if (i == 0) "  assumes " else "      and ") + binding + props + "\n"
    }

    sb ++= s"  shows $shows\n"
    if (chain_using.nonEmpty) sb ++= s"  using ${chain_using.mkString(" ")}\n"
    sb ++= s"  $proof\n"
    sb.result()
  }

  def rewrite_reference(
    source: String,
    ref_range: Text.Range,
    new_name: String,
    deps_to_prepend: List[String]
  ): Edit = {
    val replacement = discharged_ref(new_name, deps_to_prepend)

    if (deps_to_prepend.isEmpty) Edit.Replace(ref_range, replacement)
    else {
      val after = ref_range.stop
      val nxt = source.indexWhere(!_.isWhitespace, after)

      if (nxt >= 0 && source.charAt(nxt) == '[') {
        val close = find_matching_bracket(source, nxt)
        val inner = source.substring(nxt + 1, close).trim
        val new_inner =
          if (inner.startsWith("OF "))
            s"OF ${deps_to_prepend.mkString(" ")} ${inner.stripPrefix("OF ").trim}"
          else
            s"OF ${deps_to_prepend.mkString(" ")}, $inner"
        Edit.Replace(Text.Range(ref_range.start, close + 1), s"$new_name[$new_inner]")
      } else {
        Edit.Replace(ref_range, replacement)
      }
    }
  }

  def rewrite_chained_reference(
    source: String,
    command: Command,
    range: Text.Range,
    new_name: String,
    deps_to_prepend: List[String]
  ): List[Edit] = {
    val replacement = discharged_ref(new_name, deps_to_prepend)

    val keyword = command.span.name
    if (Set("then", "hence", "thus").contains(keyword)) {
      val new_text = keyword match {
        case "then"  => s"from $replacement"
        case "hence" => s"from $replacement have"
        case "thus"  => s"from $replacement show"
      }

      val keyword_range = Text.Range(range.start, range.start + keyword.length)
      List(Edit.Replace(keyword_range, new_text))
    } else Nil
  }

  def find_chained_ref_after(
    snapshot: Document.Snapshot,
    after: Text.Offset
  ): Option[(Command, Text.Range)] = {
    CommandUtils.proper_commands(snapshot, Text.Range(after, snapshot.node.source.length))
      .nextOption().collect {
        case (cmd, start) if Set("then", "hence", "thus").contains(cmd.span.name) =>
          (cmd, Text.Range(start, start + cmd.length))
      }
  }

  private def find_matching_bracket(source: String, open: Int): Int = {
    var i = open + 1
    var depth = 1
    while (i < source.length && depth > 0) {
      source.charAt(i) match {
        case '[' => depth += 1
        case ']' => depth -= 1
        case _   =>
      }
      i += 1
    }
    i - 1
  }

  def discharged_ref(name: String, deps: List[String]): String =
    if (deps.isEmpty) name
    else s"$name[OF ${deps.mkString(" ")}]"


  /* Popups */

  def prompt_lemma_name(view: View, suggested: Option[String]): Option[String] = {
    val default = suggested.getOrElse("")
    val result = JOptionPane.showInputDialog(
      view,
      "Name for the lifted lemma:",
      "Promote_Have",
      JOptionPane.QUESTION_MESSAGE,
      null, null,
      default
    )
    Option(result).map(_.toString.trim).filter(_.nonEmpty)
  }

  private def format_rejection(r: Rejected): String = {
    val parts =
      (if (r.hyps.nonEmpty) List(s"hyps: ${r.hyps.mkString(", ")}") else Nil) ++
      (if (r.fixed_in_prop.nonEmpty)
        List(s"fixed: ${r.fixed_in_prop.map { case (n, t) => s"$n :: $t" }.mkString(", ")}")
       else Nil) ++
      (if (r.local_deps.nonEmpty) List(s"deps: ${r.local_deps.mkString(", ")}") else Nil) ++
      r.other.toList
    if (parts.isEmpty) "unknown reason" else parts.mkString("; ")
  }

  private def show_rejection(view: View, r: Rejected): Unit = {
    JOptionPane.showMessageDialog(view,
      s"Cannot promote this 'have' to a top-level lemma:\n\n${format_rejection(r)}",
      "Promote_Have",
      JOptionPane.WARNING_MESSAGE)
  }
}
