lazy val annotation = (project in file("."))
  .settings(
    // Enable macro expansion
    scalacOptions += "-Ymacro-annotations",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.13.5"
  )