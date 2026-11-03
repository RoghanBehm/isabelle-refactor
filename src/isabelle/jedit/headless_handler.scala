package isabelle.jedit

import isabelle.{Document, GUI_Thread, Headless, Rendering, Sessions, Text, XML}
import javax.swing.JOptionPane
import scala.concurrent.{Promise, Await}
import scala.concurrent.duration.Duration
object Headless_Handler {

  /* Promise interrupt */
  
  def cancel(): Unit = {
    cancel_promise.foreach(_.tryFailure(new Exception("Cancelled")))
    cancel_promise = None
  }
  @volatile private var cancel_promise: Option[Promise[Document.State]] = None
  @volatile private var last_event_time: Long = System.currentTimeMillis()

  /* Proc state */

  private case class State(
      session: Headless.Session,
      resources: Headless.Resources,
      id: isabelle.UUID.T,
      doc_state: Document.State,
      theory_nodes: List[Document.Node.Name],
      dep_files: List[Document.Node.Name],
      session_name: String
  )
  private var state: Option[State] = None

  /* Proc lifetime mgmt */

  def ensure_running(
      // Start session if one isn't running
      current_file: String,
      progress: isabelle.Progress
  ): Unit = synchronized {
    if (!state.exists(s => is_same_project(s, current_file))) {
      stop()
      val s = start_fresh(current_file, progress)
      state = Some(s)
    } else {
      refresh(progress)
    }
  }
  def refresh(progress: isabelle.Progress): Unit = synchronized {
    // Ensure State object is fresh
    state.foreach { s =>
      s.resources.load_theories(
        s.session,
        s.id,
        s.theory_nodes,
        s.dep_files,
        unicode_symbols = false,
        progress
      )
      val doc_state = await_stable(s.session, s.theory_nodes, progress)
      state = Some(s.copy(doc_state = doc_state))
    }
  }
  def stop(): Unit = synchronized {
    state.foreach { s =>
      s.resources.unload_theories(s.session, s.id, s.theory_nodes)
      s.session.stop()
    }
    state = None
  }

  /* Getters */

  def snapshot(name: Document.Node.Name): Option[Document.Snapshot] =
    state.flatMap { s =>
      s.doc_state.stable_tip_version.map(v => s.doc_state.snapshot(name))
    }
  def nodes: List[Document.Node.Name] =
    state.toList.flatMap(_.theory_nodes)

  /* Internal */
  private def start_fresh(current_file: String, progress: isabelle.Progress): State = {
    // Create a fresh headless sessionn
    val p = SessionUtils.resolve_project(current_file)
    val options = PIDE.options.value
    val bg = Sessions.background(
      options,
      session = p.parent,
      dirs = JEdit_Session.session_dirs ::: p.extra_dirs
    )
    val resources = Headless.Resources(options, bg)
    val session = resources.start_session(progress = progress)
    val id = isabelle.UUID.random()

    val import_names = p.theory_short_names.map(thy =>
      resources.import_name(
        Sessions.DRAFT,
        session.master_directory(p.master_dir),
        thy
      ) -> isabelle.Position.none
    )
    val deps = resources.dependencies(import_names, progress = progress).check_errors
    val theory_nodes = deps.theories
    val dep_files = deps.loaded_files

    // Debug
    progress.echo(s"Theory nodes: ${theory_nodes.map(_.theory).mkString(", ")}")
    progress.echo(s"Dep files: ${dep_files.map(_.node).mkString(", ")}")
    //

    resources.load_theories(session, id, theory_nodes, dep_files, unicode_symbols = false, progress)
    val doc_state = await_stable(session, theory_nodes, progress)

    State(
      session,
      resources,
      id,
      doc_state,
      theory_nodes,
      dep_files,
      p.project_session
    )
  }
  private def is_same_project(s: State, file: String): Boolean = {
    // check if file belongs to the same session/ROOT
    SessionUtils.resolve_project(file).project_session == s.session_name
  }
  private def await_stable(
      // Wait for all theory nodes to be consolidated
      session: Headless.Session,
      theory_nodes: List[Document.Node.Name],
      progress: isabelle.Progress
  ): Document.State = {
    last_event_time = System.currentTimeMillis()
    val done = Promise[Document.State]()
    cancel_promise = Some(done)
    val reported = scala.collection.mutable.Set.empty[Document.Node.Name]

    val consumer = isabelle.Session.Consumer[isabelle.Session.Commands_Changed]("await_stable") {
      _ =>
        if (progress.stopped) {
          done.tryFailure(new Exception("Cancelled"))
          ()
        } else {
          last_event_time = System.currentTimeMillis()
          val state = session.get_state()
          for (version <- state.stable_tip_version) {
            for (name <- theory_nodes) {
              if (!reported.contains(name) && state.node_consolidated(version, name)) {
                reported += name
                val display_name = name.theory.stripPrefix("Draft.")

                /* error reporting needs further work */
                val snapshot = state.snapshot(name)
                val errors = collect_errors(snapshot)
                if (errors.nonEmpty) {
                  progress.echo_warning(s"Errors in $display_name: ${errors.head}")
                }
                progress.theory(isabelle.Progress.Theory(display_name, percentage = Some(100)))
              }
            }
            if (theory_nodes.forall(name => state.node_consolidated(version, name))) {
              done.trySuccess(state)
              ()
            }
          }
        }
    }
    session.commands_changed += consumer
    val state = session.get_state()
    for (version <- state.stable_tip_version) {
      if (theory_nodes.forall(name => state.node_consolidated(version, name))) {
        done.trySuccess(state)
      }
    }
    err_watcher(done.future)
    try { Await.result(done.future, Duration.Inf) }
    finally {
      session.commands_changed -= consumer
      cancel_promise = None
    }

  }
  private def collect_errors(
      snapshot: Document.Snapshot
  ): List[String] = {
    val full_range = Text.Range(0, snapshot.node.source.length)
    snapshot
      .cumulate[List[String]](
        full_range,
        Nil,
        Rendering.error_elements,
        _ => { case (acc, Text.Info(_, XML.Elem(_, body))) =>
          Some(XML.content(body).take(200) :: acc)
        }
      )
      .flatMap(_.info)
  }
  private def err_watcher(
      future: scala.concurrent.Future[Document.State]
  ): Unit = {
    val watchdog = new Thread(
      () => {
        var warned = false
        while (!future.isCompleted) {
          Thread.sleep(5000)
          val idle = System.currentTimeMillis() - last_event_time
          if (!warned && idle > 30000 && !future.isCompleted) {
            warned = true
            GUI_Thread.later {
              JOptionPane.showMessageDialog(
                null,
                "Session looks stuck, likely a syntax or proof error.\nClose the progress dialog to cancel.",
                "Warning",
                JOptionPane.WARNING_MESSAGE
              )
            }
          }
        }
      },
      "await-watchdog"
    )
    watchdog.setDaemon(true)
    watchdog.start()
  }
}
