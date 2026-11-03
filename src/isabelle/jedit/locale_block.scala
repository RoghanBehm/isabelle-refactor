package isabelle.jedit

import isabelle.{Document, Markup, Text, Rendering, Token, Command_Span, Outer_Syntax}
import org.gjt.sp.jedit.buffer.JEditBuffer

object Locale_Block {

  sealed trait Insertion
  case class IntoExisting(end: Text.Range, at: Text.Offset) extends Insertion
  case class NeedsSynthesis(after: Text.Offset) extends Insertion


  private def name_matches(target: String, name: String): Boolean =
    name == target ||
    target.endsWith("." + name) ||
    MarkupUtils.short_name(name) == MarkupUtils.short_name(target)

  def locale_def_offset(target: String, snapshot: Document.Snapshot): Option[Text.Offset] =
    MarkupUtils.collect_markup(
      snapshot, Rendering.entity_elements,
      (r, m) =>
        if (Markup.Entity.unapply(m).exists { case (kind, name) =>
              kind == "locale" && name_matches(target, name)
            } && m.properties.exists(_._1 == "def"))
          Some(r.start)
        else None
    ).headOption

  def find_insertion(
    syntax: Outer_Syntax,
    buffer: JEditBuffer,
    def_offset: Text.Offset
  ): Option[Insertion] =
    Token_Markup.command_span(syntax, buffer, def_offset).map { cmd =>
      val opens_block = cmd.info.content.exists(_.is_begin)
      if (!opens_block) NeedsSynthesis(cmd.range.stop)
      else {
        val it = Token_Markup.token_iterator(syntax, buffer, cmd.range.start).filter(_.info.is_proper)
        var depth = 0
        var started = false
        var end: Option[Text.Range] = None
        while (it.hasNext && end.isEmpty) {
          val Text.Info(range, tok) = it.next()
          if (tok.is_begin) { depth += 1; started = true }
          else if (tok.is_end) {
            depth -= 1
            if (started && depth == 0) end = Some(range)
          }
        }
        end match {
          case Some(end_range) =>
            val line = buffer.getLineOfOffset(end_range.start)
            IntoExisting(end_range, buffer.getLineStartOffset(line))  // above `end`
          case None => NeedsSynthesis(cmd.range.stop)
        }
      }
    }

}
