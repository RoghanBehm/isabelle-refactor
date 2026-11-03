package isabelle.jedit

import org.gjt.sp.jedit.View

/* This file is the entry-point for refactoring actions */


object Refactor {
  def rename(view: View): Unit = Rename(view)
  def promote_have(view: View): Unit = Promote_Have(view)
  def anti_unify(view: View): Unit = Anti_Unify(view)
  def weaken_locale(view: View): Unit = Weaken_Locale(view)
}
