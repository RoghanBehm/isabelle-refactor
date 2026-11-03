package isabelle.jedit

import isabelle.{Document, Markup, Rendering, Value, Text, XML, Sessions, GUI_Thread, Command, Keyword}
import org.gjt.sp.jedit.textarea.JEditTextArea
import java.io.{File => JFile}
import javax.swing.JOptionPane
import org.gjt.sp.jedit.View

object MarkupUtils {

  def find_markup(
      snapshot: Document.Snapshot,
      elements: Markup.Elements,
      matches: Markup => Boolean,
      range: Option[Text.Range] = None
  ): List[Text.Range] =
    collect_markup(snapshot, elements, (r, m) => if (matches(m)) Some(r) else None, range)
  def collect_markup[A](
      snapshot: Document.Snapshot,
      elements: Markup.Elements,
      extract: (Text.Range, Markup) => Option[A],
      range: Option[Text.Range] = None
  ): List[A] = {
    val search_range = range.getOrElse(Text.Range(0, snapshot.node.source.length))
    snapshot
      .cumulate[List[A]](
        search_range,
        Nil,
        elements,
        _ => {
          case (acc, Text.Info(r, XML.Elem(markup, _))) =>
            extract(r, markup).map(_ :: acc)
        }
      )
      .flatMap(_.info)
      .distinct
  }
  def short_name(qualified: String): String = {
    val dot = qualified.lastIndexOf('.')
    if (dot >= 0) qualified.substring(dot + 1) else qualified
  }

  // Return an offset to directly after the begin keyword
  def offset_after_begin(snapshot: Document.Snapshot): Option[Int] =
    find_markup(
      snapshot,
      Markup.Elements(Markup.COMMAND_SPAN),
      m => Markup.Command_Span.unapply(m).exists(_.is_begin)
    ).headOption.map(_.stop)

  /** Used by HaveGraph */

  def find_fact_refs(
    snapshot: Document.Snapshot,
    range: Text.Range
  ): List[(Long, Text.Range)] =
    collect_markup(snapshot, Rendering.entity_elements,
      (r, m) =>
      if (Markup.Entity.unapply(m).exists(_._1 == "fact"))
        m.properties.collectFirst { case ("ref", v) => v }
        .flatMap(Value.Long.unapply).map(_ -> r)
      else None,
      Some(range))

  def find_fact_ref_serials(snapshot: Document.Snapshot, range: Text.Range): List[Long] =
    find_fact_refs(snapshot, range).map(_._1).distinct

  def find_fact_defs(snapshot: Document.Snapshot, range: Text.Range): List[(Long, Text.Range)] =
    collect_markup(snapshot, Rendering.entity_elements,
      (r, m) =>
      if (Markup.Entity.unapply(m).exists(_._1 == "fact"))
        m.properties.collectFirst { case ("def", v) => v }
        .flatMap(Value.Long.unapply).map(_ -> r)
      else None,
      Some(range))

  /** */
}

object JEditUtils {


  /* UI */

  def progress_dialog(
      view: View
  ): (javax.swing.JDialog, javax.swing.JLabel) = {
    val dialog = new javax.swing.JDialog(view, "Renaming…", true)
    val label = new javax.swing.JLabel("Loading theories…")
    val progress_bar = new javax.swing.JProgressBar()
    progress_bar.setIndeterminate(true)
    val panel = new javax.swing.JPanel()
    panel.setLayout(new javax.swing.BoxLayout(panel, javax.swing.BoxLayout.Y_AXIS))
    panel.setBorder(javax.swing.BorderFactory.createEmptyBorder(20, 20, 20, 20))
    panel.add(label)
    panel.add(javax.swing.Box.createVerticalStrut(10))
    panel.add(progress_bar)
    dialog.add(panel)
    dialog.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE)
    dialog.pack()
    dialog.setLocationRelativeTo(view)
    (dialog, label)
  }
  def theory_progress(label: javax.swing.JLabel): isabelle.Progress =
    new isabelle.Progress {
      override def output(msgs: isabelle.Progress.Output): Unit =
        for (msg <- msgs) msg match {
          case thy: isabelle.Progress.Theory =>
            GUI_Thread.later { label.setText(s"Checking ${thy.theory}…") }
          case _ =>
        }
    }
  def select_dialog[A](
    view: View,
    title: String,
    entries: List[A],
    label: A => String,
    preselected: Boolean = false,
    width: Int = 560,
    max_height: Int = 400
  ): List[A] = {
    val boxes = entries.map(e => (new javax.swing.JCheckBox(label(e), preselected), e))

    val panel = new javax.swing.JPanel()
    panel.setLayout(new javax.swing.BoxLayout(panel, javax.swing.BoxLayout.Y_AXIS))
    boxes.foreach { case (cb, _) => panel.add(cb) }

    val scroll = new javax.swing.JScrollPane(panel)
    scroll.setPreferredSize(
      new java.awt.Dimension(width, (entries.size * 26 + 8) min max_height))

    val choice = JOptionPane.showConfirmDialog(
      view, scroll, title, JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE)

    if (choice == JOptionPane.OK_OPTION)
      boxes.collect { case (cb, e) if cb.isSelected => e }
    else Nil
  }
}

object SessionUtils {

  /** Walk upward from `start` looking for a session root directory. Prefers directories containing
    * ROOTS; falls back to ROOT.
    */
  def find_session_dir(start: JFile): Option[isabelle.Path] = {
    var roots_dir: Option[JFile] = None
    var root_dir: Option[JFile] = None
    var d = start

    while (d != null) {
      if (roots_dir.isEmpty && new JFile(d, "ROOTS").exists()) roots_dir = Some(d)
      if (root_dir.isEmpty && new JFile(d, "ROOT").exists()) root_dir = Some(d)
      d = d.getParentFile
    }

    roots_dir.orElse(root_dir).map(f => isabelle.Path.explode(f.getPath))
  }

  /* Project resolution */

  case class ProjectInfo(
      project_session: String,
      parent: String,
      theory_short_names: List[String],
      master_dir: String,
      extra_dirs: List[isabelle.Path]
  )
  def resolve_project(current_file: String): ProjectInfo = {
    val options = PIDE.options.value
    val dir = new JFile(current_file).getParent
    val extra_dirs = find_session_dir(new JFile(dir)).toList
    val sessions =
      JEdit_Session.sessions_structure(dirs = JEdit_Session.session_dirs ::: extra_dirs)
    val project_session = sessions.session_directories
      .get(new JFile(dir).getCanonicalFile)
      .getOrElse(JEdit_Session.logic_name(options))
    val info = sessions(project_session)
    val parent = info.parent.getOrElse(JEdit_Session.logic_name(options))
    val theory_short_names = info.theories.flatMap(_._2.map(_._1))
    val master_dir = info.dir.implode
    ProjectInfo(project_session, parent, theory_short_names, master_dir, extra_dirs)
  }

}


object CommandUtils {
  def proper_commands(
    snapshot: Document.Snapshot,
    scope: Text.Range
  ): Iterator[(Command, Text.Offset)] =
    snapshot.node.command_iterator(scope.start)
      .takeWhile { case (_, start) => start < scope.stop }
      .filter(_._1.is_proper)

  def find_commands[A](
    snapshot: Document.Snapshot,
    scope: Text.Range
  )(extract: (Command, Text.Offset) => Option[A]): List[A] =
    proper_commands(snapshot, scope).flatMap { case (cmd, start) =>
      extract(cmd, start)
    }.toList

  def head_name(command: Command): Option[String] =
    command.span.clean_arguments.headOption.collect {
      case (tok, _) if tok.is_name => tok.source
    }

  def qed_end(snapshot: Document.Snapshot, goal_start: Text.Offset): Option[Text.Offset] = {
    val kw = snapshot.node.syntax.map(_.keywords)   
    def delta(name: String): Int = kw.flatMap(_.kinds.get(name)) match {
      case Some(k) if Keyword.theory_goal(k) || Keyword.proof_goal(k) || Keyword.proof_open(k)  =>  1
      case Some(k) if Keyword.qed(k) || Keyword.qed_global(k) || Keyword.proof_close(k)         => -1
      case _ => 0
    }
    val it = proper_commands(snapshot, Text.Range(goal_start, snapshot.node.source.length))
    var depth = 0; var end: Option[Text.Offset] = None; var stop = false
    while (it.hasNext && !stop) {
      val (cmd, start) = it.next()
      depth += delta(cmd.span.name)
      end = Some(start + cmd.length)
      if (depth <= 0) stop = true
    }
    if (stop) end else None
  }

}
