package kuplrg

trait Template {

  def eval(str: String): String =
    val expr = Expr(str)
    val ty = typeCheck(expr, TypeEnv()).str
    val result =
      try interp(expr, Map.empty).str
      catch case e: PLError => "ERROR"
    s"$result: $ty"

  def typeCheck(expr: Expr, tenv: TypeEnv): Type

  def interp(expr: Expr, env: Env): Value

}
