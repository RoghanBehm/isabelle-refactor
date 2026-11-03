package isabelle.jedit

import isabelle.{Text, Path, File, Document}

sealed trait Edit {
  def range: Text.Range
  def new_text: String
}

object Edit {
  case class Replace(range: Text.Range, new_text: String) extends Edit
  case class Insert(offset: Int, new_text: String) extends Edit {
    def range: Text.Range = Text.Range(offset, offset)
  }
  case class Delete(range: Text.Range) extends Edit {
    def new_text: String = ""
  }

  /** String write */
  def apply_to_text(text: String, edits: List[Edit]): String = {
    val sorted = edits.sortBy(-_.range.start)
    check_no_overlap(sorted)
    sorted.foldLeft(text) { (t, e) =>
      t.substring(0, e.range.start) + e.new_text + t.substring(e.range.stop)
    }
  }



  /** jEdit buffer write */
  def apply_to_buffer(buffer: org.gjt.sp.jedit.Buffer, edits: List[Edit]): Unit = {
    val sorted = edits.sortBy(-_.range.start)
    check_no_overlap(sorted)
    buffer.beginCompoundEdit()
    try {
      sorted.foreach {
        case Replace(range, new_text) =>
          buffer.remove(range.start, range.length)
          buffer.insert(range.start, new_text)
        case Insert(offset, new_text) =>
          buffer.insert(offset, new_text)
        case Delete(range) =>
          buffer.remove(range.start, range.length)
      }
    } finally {
      buffer.endCompoundEdit()
    }
  }


  private def check_no_overlap(sorted_desc: List[Edit]): Unit = {
    sorted_desc.sliding(2).foreach {
      case List(a, b) if b.range.stop > a.range.start =>
        throw new IllegalArgumentException(s"Overlapping edits: $a vs $b")
      case _ =>
    }
  }

}
