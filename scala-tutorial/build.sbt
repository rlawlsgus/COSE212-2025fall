ThisBuild / scalaVersion := "3.3.3"
ThisBuild / scalacOptions ++= Seq(
  "-feature",
  "-deprecation",
  "-explain",
  "-explain-types",
  "-language:implicitConversions",
)

lazy val root = project
  .in(file("."))
  .settings(
    name := "scala-tutorial",
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.15" % Test,
    wartremoverClasspaths += "file://" + baseDirectory.value + "/lib/warts.jar",
    wartremoverErrors ++= Seq(
      Wart.AsInstanceOf,
      Wart.IsInstanceOf,
      Wart.MutableDataStructures,
      Wart.Null,
      Wart.Return,
      Wart.Throw,
      Wart.Var,
      Wart.While,
      Wart.custom("kuplrg.warts.Array"),
      Wart.custom("kuplrg.warts.TryCatch"),
    ),
    wartremoverExcluded ++= Seq(
      baseDirectory.value / "src" / "main" / "scala" / "kuplrg" / "Template.scala",
      baseDirectory.value / "src" / "main" / "scala" / "kuplrg" / "error.scala",
      baseDirectory.value / "src" / "test" / "scala" / "kuplrg",
    ),
  )

run := (root / Compile / run).evaluated
test := (root / Test / test).value
Test / testOptions += Tests
  .Argument("-fDG", baseDirectory.value + "/test-detail")

// format all files
lazy val format = taskKey[Unit]("format all files")
format := Def
  .sequential(
    Compile / scalafmtAll,
    Compile / scalafmtSbt,
  )
  .value
