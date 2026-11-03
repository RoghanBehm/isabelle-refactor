package isabelle.jedit
import isabelle.{GUI_Thread, Query_Operation, Editor, XML, Markup, Text, Command, Keyword}
import org.gjt.sp.jedit.View
import javax.swing.JOptionPane

object Anti_Unify {
  val lemma_kw = Set("lemma", "theorem", "corollary", "proposition")

  def apply(view: View): Unit = GUI_Thread.now {
    val text_area = view.getTextArea
    Document_View.get(text_area).foreach { doc_view =>
      val snapshot = Document_View.rendering(doc_view).snapshot
      val scope = Text.Range(0, snapshot.node.source.length)

      // For each lemma: its name, where it starts, and the range of its proof
      val cmds = CommandUtils.proper_commands(snapshot, scope).toList
      val keywords = Isabelle.buffer_syntax(view.getBuffer).map(_.keywords)
      def kind(c: Command): String = keywords.flatMap(_.kinds.get(c.span.name)).getOrElse("")

      val lemmas: List[(String, (Int, Text.Range, Command))] =
        cmds.zipWithIndex.flatMap { case ((cmd, start), i) =>
          if (!lemma_kw(cmd.span.name)) None
          else CommandUtils.head_name(cmd).map { n =>
            val stmt_end = start + cmd.length
            val prf = cmds.drop(i + 1)
              .takeWhile { case (c, _) => !Keyword.theory(kind(c)) }
              .reverse.dropWhile { case (c, _) => !Keyword.proof(kind(c)) }.reverse
            val prf_range = (prf.headOption, prf.lastOption) match {
              case (Some((_, s0)), Some((c1, s1))) => Text.Range(s0, s1 + c1.length)
              case _ => Text.Range(stmt_end, stmt_end)
            }
            n -> (start, prf_range, cmd)
          }
        }
      val names = lemmas.map(_._1)
      val pos = lemmas.toMap

      for {
        n1 <- pick(view, "First lemma:", names)
        n2 <- pick(view, "Second lemma:", names.filterNot(_ == n1))
      } {
        val saved = text_area.getCaretPosition
        val ctx_off: Int =
          CommandUtils.proper_commands(snapshot, Text.Range(0, snapshot.node.source.length)).toList
            .filterNot { case (c, _) => c.span.name == "end" }
            .lastOption
            .map { case (c, start) => start + c.length - 1 }
            .getOrElse(text_area.getCaretPosition)
        text_area.setCaretPosition(ctx_off)

        val q = new Query_Operation(PIDE.editor, view, "anti_unify",
          (st: Query_Operation.Status) =>
            if (st == Query_Operation.Status.finished)
              GUI_Thread.later { text_area.setCaretPosition(saved) },
          (out: Editor.Output) => GUI_Thread.later {
            out.messages.collectFirst {
              case XML.Elem(_, List(XML.Elem(Markup("anti_unify", _), body))) => XML.content(body)
            } match {
              case Some(stmt) =>
                Option(JOptionPane.showInputDialog(view, "Name for the generalised lemma:",
                    "Anti-unify", JOptionPane.QUESTION_MESSAGE, null, null, "anti_unified"))
                  .map(_.toString.trim).filter(_.nonEmpty) match {
                  case Some(name) =>
                    // The general lemma goes just before the earlier source lemma.
                    // Source lemmas have their proofs changed to instantiation of the
                    // generalising lemma.
                    val (start1, prf1, cmd1) = pos(n1)
                    val (start2, prf2, cmd2) = pos(n2)
                    val txt = s"lemma $name:\n$stmt\n  sorry\n\n"

                    // Special handling of "assumes" and "if" proofs.
                    def instance_proof(c: Command): String = {
                      def has(kw: String) = c.span.content.exists(t => t.is_keyword && t.source == kw)
                      if (has("assumes")) s"using assms by (rule $name)"
                      else if (has("if")) s"using that by (rule $name)"
                      else s"by (fact $name)"
                    }
                    val instance_proofs = List((prf1, cmd1), (prf2, cmd2))
                      .map { case (r, c) => Edit.Replace(r, instance_proof(c)) }
                    Edit.apply_to_buffer(view.getBuffer,
                      Edit.Insert(start1 min start2, txt) :: instance_proofs)
                  case None => // name prompt cancelled
                }
              case None =>
                out.messages.collectFirst {
                  case XML.Elem(_, List(XML.Elem(Markup("anti_unify_error", _), body))) =>
                    "anti_unify raised:\n\n" + XML.content(body)
                }.foreach { detail =>
                  JOptionPane.showMessageDialog(view, detail, "Anti-unify failed", JOptionPane.ERROR_MESSAGE)
                }
            }
          })
        q.activate(); q.apply_query(List(n1, n2))
      }
    }
  }

  private def pick(view: View, msg: String, ns: List[String]): Option[String] =
    Option(JOptionPane.showInputDialog(view, msg, "Anti-unify",
      JOptionPane.QUESTION_MESSAGE, null, ns.toArray[AnyRef], ns.headOption.orNull)).map(_.toString)
}
