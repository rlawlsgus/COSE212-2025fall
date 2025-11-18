package kuplrg

object Implementation extends Template {

  import Stmt.*, Expr.*, Value.*, BOp.*, Inst.*, Control.*, Error.*

  def reduce(st: State): State =
    val State(k, s, h, m) = st
    k.head match
      // Block
      case IBlock(env, block) =>
        val newK = block.stmts.map(IStmt(env, _)) ::: k.tail
        st.copy(cont = newK)

      // Statements
      case IStmt(env, stmt) => stmt match
        case SPass =>
          st.copy(cont = k.tail)
        case SExpr(expr) =>
          st.copy(cont = IExpr(env, expr) :: IDrop :: k.tail)
        case SAssign(name, expr) =>
          st.copy(cont = IExpr(env, expr) :: IWrite(env(name)) :: k.tail)
        case SSetItem(base, idx, expr) =>
          st.copy(cont = IExpr(env, expr) :: IExpr(env, base) :: IExpr(env, idx) :: ISetItem :: k.tail)
        case SIf(cond, thenB, elseB) =>
          val thenK = IBlock(env, thenB) :: k.tail
          val elseK = IBlock(env, elseB) :: k.tail
          val kValue = KValue(elseK, s, h)
          st.copy(cont = IExpr(env, cond) :: IJmpIf(kValue) :: thenK)
        case SWhile(cond, body) =>
          val loopK = IExpr(env, cond) :: IJmpIf(KValue(k.tail, s, h)) :: IBlock(env, body) :: k
          val kValueContinue = KValue(k, s, h)
          val kValueBreak = KValue(k.tail, s, h)
          val newH = h + (Continue -> kValueContinue) + (Break -> kValueBreak)
          st.copy(cont = loopK, handler = newH)
        case SBreak =>
          st.copy(cont = IJmp(Break) :: k.tail)
        case SContinue =>
          st.copy(cont = IJmp(Continue) :: k.tail)
        case STry(body, except) =>
          val finallyKValue = KValue(k.tail, s, h)
          val raiseKValue = KValue(IBlock(env, except) :: k.tail, s, h)
          val newH = h + (Finally -> finallyKValue) + (Raise -> raiseKValue)
          st.copy(cont = IBlock(env, body) :: IJmp(Finally) :: k.tail, handler = newH)
        case SRaise =>
          st.copy(cont = IRaise(RuntimeError) :: k.tail)
        case SDef(name, params, body) =>
          val v = if (hasYield(body)) Value.GenV(params, body, env) else Value.CloV(params, body, env)
          st.copy(cont = k.tail, mem = m + (env(name) -> v))
        case SReturn(expr) =>
          st.copy(cont = IExpr(env, expr) :: IReturn :: k.tail)
        case SYield(expr) =>
          st.copy(cont = IExpr(env, expr) :: IYield :: k.tail)

      // Expressions
      case IExpr(env, expr) => expr match
        case ENone =>
          st.copy(cont = k.tail, stack = Value.NoneV :: s)
        case ENum(n) =>
          st.copy(cont = k.tail, stack = Value.NumV(n) :: s)
        case EBool(b) =>
          st.copy(cont = k.tail, stack = Value.BoolV(b) :: s)
        case EId(name) =>
          env.get(name) match
            case Some(addr) => m.get(addr) match
              case Some(value) => st.copy(cont = k.tail, stack = value :: s)
              case None => kuplrg.error(s"address error: $addr")
            case None => st.copy(cont = IRaise(NameError(name)) :: Nil, stack = s)
        case EBOp(op, left, right) =>
          st.copy(cont = IExpr(env, left) :: IExpr(env, right) :: IBOp(op) :: k.tail)
        case EList(elems) =>
          val newK = elems.map(IExpr(env, _)) ::: IList(elems.length) :: k.tail
          st.copy(cont = newK)
        case EGetItem(base, idx) =>
          st.copy(cont = IExpr(env, base) :: IExpr(env, idx) :: IGetItem :: k.tail)
        case EAppend(list, elem) =>
          st.copy(cont = IExpr(env, list) :: IExpr(env, elem) :: IAppend :: k.tail)
        case ECond(cond, thenE, elseE) =>
          val thenK = IExpr(env, thenE) :: k.tail
          val elseK = IExpr(env, elseE) :: k.tail
          val kValue = KValue(elseK, s, h)
          st.copy(cont = IExpr(env, cond) :: IJmpIf(kValue) :: thenK)
        case ELambda(params, body) =>
          val newAddr = m.keys.maxOption.getOrElse(-1) + 1
          val clo = Value.CloV(params, Block(List(SReturn(body))), env)
          st.copy(cont = k.tail, stack = Value.AddrV(newAddr) :: s, mem = m + (newAddr -> clo))
        case EApp(fun, args) =>
          val newK = IExpr(env, fun) :: args.map(IExpr(env, _)) ::: ICall(args.length) :: k.tail
          st.copy(cont = newK)
        case EIter(expr) =>
          st.copy(cont = IExpr(env, expr) :: IIter :: k.tail)
        case ENext(expr) =>
          st.copy(cont = IExpr(env, expr) :: INext :: k.tail)

      // Instructions
      case IBOp(op) =>
        val v2 :: v1 :: s_ = s
        (op, v1, v2) match
          case (Add, Value.NumV(n1), Value.NumV(n2)) => st.copy(cont = k.tail, stack = Value.NumV(n1 + n2) :: s_)
          case (Mul, Value.NumV(n1), Value.NumV(n2)) => st.copy(cont = k.tail, stack = Value.NumV(n1 * n2) :: s_)
          case (Div, _, Value.NumV(n)) if n == 0 => st.copy(cont = IRaise(ZeroDivisionError) :: Nil, stack = s)
          case (Div, Value.NumV(n1), Value.NumV(n2)) => st.copy(cont = k.tail, stack = Value.NumV(n1 / n2) :: s_)
          case (Mod, _, Value.NumV(n)) if n == 0 => st.copy(cont = IRaise(ZeroDivisionError) :: Nil, stack = s)
          case (Mod, Value.NumV(n1), Value.NumV(n2)) => st.copy(cont = k.tail, stack = Value.NumV(n1 % n2) :: s_)
          case (Lt, _, _) => lessThan(v1, v2, m) match
            case Some(b) => st.copy(cont = k.tail, stack = Value.BoolV(b) :: s_)
            case None => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
          case (Lte, _, _) => lessThan(v2, v1, m) match
            case Some(b) => st.copy(cont = k.tail, stack = Value.BoolV(!b) :: s_)
            case None => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
          case (Eq, _, _) => st.copy(cont = k.tail, stack = Value.BoolV(equal(v1, v2, m)) :: s_)
          case (Is, _, _) => st.copy(cont = k.tail, stack = Value.BoolV(is(v1, v2)) :: s_)
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)

      case IWrite(addr) =>
        val v :: s_ = s
        st.copy(cont = k.tail, stack = s_, mem = m + (addr -> v))

      case IDrop =>
        val _ :: s_ = s
        st.copy(cont = k.tail, stack = s_)

      case IList(n) =>
        val (elems, s_) = s.splitAt(n)
        val newAddr = m.keys.maxOption.getOrElse(-1) + 1
        st.copy(cont = k.tail, stack = Value.AddrV(newAddr) :: s_, mem = m + (newAddr -> Value.ListV(elems.reverse)))

      case IGetItem =>
        val idxV :: baseV :: s_ = s
        (m.get(baseV), m.get(idxV)) match
          case (Some(Value.ListV(list)), Some(Value.NumV(idx))) =>
            val i = idx.toInt
            if (i >= 0 && i < list.length) st.copy(cont = k.tail, stack = list(i) :: s_)
            else if (i < 0 && i >= -list.length) st.copy(cont = k.tail, stack = list(list.length + i) :: s_)
            else st.copy(cont = IRaise(IndexError) :: Nil, stack = s)
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)

      case ISetItem =>
        val idxV :: baseV :: valV :: s_ = s
        (baseV, idxV) match
          case (Value.AddrV(addr), Value.NumV(idx)) => m(addr) match
            case Value.ListV(list) =>
              val i = idx.toInt
              if (i >= 0 && i < list.length) {
                val newList = list.updated(i, valV)
                st.copy(cont = k.tail, stack = s_, mem = m + (addr -> Value.ListV(newList)))
              } else if (i < 0 && i >= -list.length) {
                val newList = list.updated(list.length + i, valV)
                st.copy(cont = k.tail, stack = s_, mem = m + (addr -> Value.ListV(newList)))
              } else {
                st.copy(cont = IRaise(IndexError) :: Nil, stack = s)
              }
            case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)

      case IAppend =>
        val elemV :: listV :: s_ = s
        listV match
          case Value.AddrV(addr) => m(addr) match
            case Value.ListV(list) =>
              val newList = list :+ elemV
              st.copy(cont = k.tail, stack = listV :: s_, mem = m + (addr -> Value.ListV(newList)))
            case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)

      case IJmpIf(kValue) =>
        val v :: s_ = s
        if (isTruthy(v, m)) st.copy(cont = k.tail, stack = s_)
        else st.copy(cont = kValue.cont, stack = kValue.stack, handler = kValue.handler)

      case IJmp(control) =>
        val kValue = h(control)
        st.copy(cont = kValue.cont, stack = kValue.stack, handler = kValue.handler)

      case IRaise(error) =>
        h.get(Raise) match
          case Some(kValue) => st.copy(cont = kValue.cont, stack = kValue.stack, handler = kValue.handler)
          case None => kuplrg.error(error.str)

      case ICall(n) =>
        val (args, s_) = s.splitAt(n)
        val funV :: s__ = s_
        m.get(funV) match
          case Some(Value.CloV(params, body, env)) =>
            if (params.length != n) st.copy(cont = IRaise(TypeError) :: Nil, stack = s) else {
            val (m1, env1) = params.zip(args.reverse).foldLeft((m, env)) {
              case ((curM, curEnv), (name, value)) =>
                val newAddr = curM.keys.maxOption.getOrElse(-1) + 1
                (curM + (newAddr -> value), curEnv + (name -> newAddr))
            }
            val (m2, env2) = (locals(body) -- params).foldLeft((m1, env1)) {
              case ((curM, curEnv), name) =>
                val newAddr = curM.keys.maxOption.getOrElse(-1) + 1
                (curM + (newAddr -> Value.NoneV), curEnv + (name -> newAddr))
            }
            val returnKValue = KValue(k.tail, s__, h)
            val newH = h -- List(Break, Continue, Yield) + (Return -> returnKValue)
            st.copy(cont = IBlock(env2, body) :: IExpr(env2, ENone) :: IReturn :: Nil, stack = Nil, handler = newH, mem = m2)
            }
          case Some(Value.GenV(params, body, env)) =>
            if (params.length != n) {
              st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
            } else {
              val (m1, env1) = params.zip(args.reverse).foldLeft((m, env)) {
                case ((curM, curEnv), (name, value)) =>
                  val newAddr = curM.keys.maxOption.getOrElse(-1) + 1
                  (curM + (newAddr -> value), curEnv + (name -> newAddr))
              }
              val (m2, env2) = (locals(body) -- params).foldLeft((m1, env1)) {
                case ((curM, curEnv), name) =>
                  val newAddr = curM.keys.maxOption.getOrElse(-1) + 1
                  (curM + (newAddr -> Value.NoneV), curEnv + (name -> newAddr))
              }
              val kValue = KValue(IBlock(env2, body) :: IExpr(env2, ENone) :: IReturn :: Nil, Nil, h)
              val contAddr = m2.keys.maxOption.getOrElse(-1) + 1
              val iterAddr = contAddr + 1
              val newM = m2 + (contAddr -> Value.ContV(kValue)) + (iterAddr -> Value.IterV(contAddr, 0))
              st.copy(cont = k.tail, stack = Value.AddrV(iterAddr) :: s__, mem = newM)
            }
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)

      case IReturn =>
        val v :: _ = s
        h.get(Return) match
          case Some(kValue) => st.copy(cont = kValue.cont, stack = v :: kValue.stack, handler = kValue.handler)
          case None => st.copy(cont = Nil, stack = v :: Nil)

      case IYield =>
        val v :: s_ = s
        s_ match {
          case Value.AddrV(contAddr) :: genStack =>
            val kValue = KValue(k.tail, genStack, h)
            val newM = m + (contAddr -> Value.ContV(kValue))
            val yieldKValue = h(Yield)
            st.copy(cont = yieldKValue.cont, stack = v :: yieldKValue.stack, handler = yieldKValue.handler, mem = newM)
          case _ => kuplrg.error("stack error in IYield")
        }

      case IIter =>
        val v :: s_ = s
        v match {
          case addrV @ Value.AddrV(addr) => m.get(addr) match {
            case Some(_: Value.ListV) =>
              val iterAddr = m.keys.maxOption.getOrElse(-1) + 1
              val newM = m + (iterAddr -> Value.IterV(addr, 0))
              st.copy(cont = k.tail, stack = Value.AddrV(iterAddr) :: s_, mem = newM)
            case Some(_: Value.IterV) =>
              st.copy(cont = k.tail, stack = addrV :: s_)
            case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
          }
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
        }

      case INext =>
        val v :: s_ = s
        v match {
          case Value.AddrV(iterAddr) =>
            m.get(iterAddr) match {
              case Some(Value.IterV(targetAddr, idx)) =>
                m.get(targetAddr) match {
                  case Some(Value.ContV(kValue)) =>
                    val yieldKValue = KValue(k.tail, s_, h)
                    val returnKValue = KValue(IRaise(StopIteration) :: Nil, Nil, h)
                    val newH = kValue.handler + (Yield -> yieldKValue) + (Return -> returnKValue)
                    val genStack = Value.AddrV(targetAddr) :: kValue.stack
                    st.copy(cont = kValue.cont, stack = genStack, handler = newH, mem = m)
                  case Some(Value.ListV(list)) =>
                    if (idx < list.length) {
                      val newM = m + (iterAddr -> Value.IterV(targetAddr, idx + 1))
                      st.copy(cont = k.tail, stack = list(idx) :: s_, mem = newM)
                    } else {
                      st.copy(cont = IRaise(StopIteration) :: Nil, stack = s)
                    }
                  case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
                }
              case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
            }
          case _ => st.copy(cont = IRaise(TypeError) :: Nil, stack = s)
        }

  def locals(block: Block): Set[String] =
    localsInListOfStmt(block.stmts)

  def localsInListOfStmt(stmts: List[Stmt]): Set[String] =
    stmts.foldLeft(Set[String]()) {
      case (acc, stmt) => acc ++ localsInStmt(stmt)
    }

  def localsInStmt(stmt: Stmt): Set[String] = stmt match
    case SAssign(name, _)       => Set(name)
    case SDef(name, _, _)       => Set(name)
    case SIf(_, thenB, elseB)   => locals(thenB) ++ locals(elseB)
    case SWhile(_, body)        => locals(body)
    case STry(body, except)     => locals(body) ++ locals(except)
    case _                      => Set.empty
  }

  def hasYield(block: Block): Boolean =
    hasYieldInListOfStmt(block.stmts)

  def hasYieldInListOfStmt(stmts: List[Stmt]): Boolean =
    stmts.exists(hasYieldInStmt)

  def hasYieldInStmt(stmt: Stmt): Boolean = stmt match
    case Stmt.SYield(_)              => true
    case Stmt.SDef(_, _, body)       => hasYield(body)
    case Stmt.SIf(_, thenB, elseB)   => hasYield(thenB) || hasYield(elseB)
    case Stmt.SWhile(_, body)        => hasYield(body)
    case Stmt.STry(body, except)     => hasYield(body) || hasYield(except)
    case _                      => false

  def is(v1: Value, v2: Value): Boolean = (v1, v2) match
    case (Value.NoneV, Value.NoneV) => true
    case (Value.NumV(n1), Value.NumV(n2)) => n1 == n2
    case (Value.BoolV(b1), Value.BoolV(b2)) => b1 == b2
    case (Value.AddrV(a1), Value.AddrV(a2)) => a1 == a2
    case _ => false

  def equal(v1: Value, v2: Value, m: Mem): Boolean = (v1, v2) match
    case (Value.AddrV(a1), Value.AddrV(a2)) => if (a1 == a2) true else equal(m(a1), m(a2), m)
    case (Value.ListV(l1), Value.ListV(l2)) =>
      l1.length == l2.length && l1.zip(l2).forall { case (e1, e2) => equal(e1, e2, m) }
    case (_: Value.CloV, _: Value.CloV) => v1 eq v2
    case (_: Value.GenV, _: Value.GenV) => v1 eq v2
    case _ => is(v1, v2)

  def lessThan(v1: Value, v2: Value, m: Mem): Option[Boolean] = (v1, v2) match
    case (Value.NumV(n1), Value.NumV(n2)) => Some(n1 < n2)
    case (Value.AddrV(a1), Value.AddrV(a2)) => lessThan(m(a1), m(a2), m)
    case (Value.ListV(l1), Value.ListV(l2)) =>
      (l1, l2) match
        case (Nil, Nil) => Some(false)
        case (Nil, _) => Some(true)
        case (_, Nil) => Some(false)
        case (h1 :: t1, h2 :: t2) =>
          lessThan(h1, h2, m) match
            case Some(true) => Some(true)
            case Some(false) =>
              if (equal(h1, h2, m)) lessThan(Value.ListV(t1), Value.ListV(t2), m)
              else Some(false)
            case None => None
    case _ => None

  def isTruthy(v: Value, m: Mem): Boolean = v match
    case Value.NoneV => false
    case Value.NumV(n) => n != 0
    case Value.BoolV(b) => b
    case Value.AddrV(a) => m.get(a).exists(isTruthy(_, m))
    case Value.ListV(l) => l.nonEmpty
    case _ => true
  
  extension (mem: Mem) def get(v: Value): Option[Value] = v match
    case Value.AddrV(addr) => mem.get(addr)
    case _ => Some(v)