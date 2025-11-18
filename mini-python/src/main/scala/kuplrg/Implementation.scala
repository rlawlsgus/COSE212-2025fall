package kuplrg

object Implementation extends Template {

  import Stmt.*, Expr.*, Value.*, BOp.*, Inst.*, Control.*, Error.*

  def reduce(st: State): State =
    val State(k, s, h, m) = st
    ???

  def locals(block: Block): Set[String] = ???
}
