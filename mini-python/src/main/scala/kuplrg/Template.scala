package kuplrg

trait Template {

  import Inst.*

  def eval(str: String, debug: Boolean = false): String =
    def aux(st: State): String =
      if (debug) log(st.str)
      st match
        case State(Nil, List(v), _, mem) =>
          val result = v.str(mem)
          if (debug) log("Result: " + result)
          result
        case _ => aux(reduce(st))
    def log(msg: String): Unit = println("-" * 80 + "\n" + msg)
    val Program(stmts, expr) = Program(str)
    val xs = if (stmts.isEmpty) Nil else locals(Block(stmts)).toList
    val addrs = (0 until xs.size)
    val mem = addrs.map(_ -> Value.NoneV).toMap
    val env = (xs zip addrs).toMap
    val initK = stmts.map(IStmt(env, _)) ::: IExpr(env, expr) :: Nil
    val initSt = State(initK, Nil, Map.empty, mem)
    aux(initSt)

  def reduce(st: State): State

  def locals(block: Block): Set[String]
}
