ThisBuild / scalaVersion := "3.3.4"

val isabelleHome = file("/Applications/Isabelle2025-2.app")

Compile / scalaSource := baseDirectory.value / "src"

Compile / unmanagedJars ++= {
  val contrib = isabelleHome / "contrib"
  val pure    = isabelleHome / "lib" / "classes"

  Seq(
    pure    / "isabelle.jar",
    contrib / "flatlaf-3.6.2" / "lib" / "flatlaf-3.6.2-no-natives.jar",
    contrib / "flatlaf-3.6.2" / "lib" / "flatlaf-extras-3.6.2.jar",
    contrib / "isabelle_setup-20250613" / "lib" / "isabelle_setup.jar",
    contrib / "jedit-20251128" / "jedit5.7.0-patched" / "jedit.jar",
    contrib / "jsoup-1.21.2" / "lib" / "jsoup-1.21.2.jar"
  ).filter(_.exists).map(Attributed.blank(_))
}

autoScalaLibrary := false
libraryDependencies += "org.scala-lang" % "scala3-library_3" % "3.3.4"
