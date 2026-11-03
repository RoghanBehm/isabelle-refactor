package isabelle.jedit

import isabelle.{Document, Markup, Rendering, Text, Value, XML, Command, Token}


case class HaveNode(range: Text.Range, source: String, command: Command) {
  def head_range: Text.Range = Text.Range(range.start, range.start + command.length)

  def parse_head: (Option[String], Option[String]) = {
    val args = command.span.clean_arguments
    val name = args.headOption.collect {
      case (tok, _) if tok.is_name => tok.source
    }
    val prop = args.collectFirst {
      case (tok, _) if tok.is_string ||
          tok.kind == Token.Kind.CARTOUCHE ||
          tok.kind == Token.Kind.ALT_STRING =>
        tok.source
    }
    (name, prop)
  }
}

case class HaveGraph(
    nodes: Map[Text.Offset, HaveNode],
    deps: Map[Text.Offset, List[Text.Offset]]
) {
  def reachable_(start: Text.Offset): List[HaveNode] = ???
}

object HaveGraph {
  def build(snapshot: Document.Snapshot, scope: Text.Range): HaveGraph = {

    val haves: List[HaveNode] =
      Promote_Have.collect_sibling_haves(snapshot, scope)
    val nodes: Map[Text.Offset, HaveNode] =
      haves.map(node => node.range.start -> node).toMap


    val serial_to_have: Map[Long, Text.Offset] =
      haves.map { node =>
        // Get% serials pointing inside currently matched
        // `have` block, map to `have` start offset
        MarkupUtils.find_fact_defs(snapshot, node.head_range).map {
          case (serial, _) => serial -> node.range.start
        }
      }.flatten.toMap

    val deps: Map[Text.Offset, List[Text.Offset]] =
      haves.map { node =>
        val edges =
          MarkupUtils
            .find_fact_ref_serials(snapshot, node.range) // get serials
            .flatMap(serial_to_have.get)
            .distinct
        node.range.start -> edges // map `have` offset too its deps
      }.toMap


    HaveGraph(nodes, deps)
  }
}
