error id: file:///C:/Users/jh062/Documents/GitHub/COSE212-2025fall/mini-fsharp/src/main/scala/kuplrg/Implementation.scala:`<none>`.
file:///C:/Users/jh062/Documents/GitHub/COSE212-2025fall/mini-fsharp/src/main/scala/kuplrg/Implementation.scala
empty definition using pc, found symbol in pc: `<none>`.
empty definition using semanticdb
empty definition using fallback
non-local guesses:
	 -Expr.e1.
	 -Expr.e1#
	 -Expr.e1().
	 -Value.e1.
	 -Value.e1#
	 -Value.e1().
	 -Pattern.e1.
	 -Pattern.e1#
	 -Pattern.e1().
	 -e1.
	 -e1#
	 -e1().
	 -scala/Predef.e1.
	 -scala/Predef.e1#
	 -scala/Predef.e1().
offset: 2654
uri: file:///C:/Users/jh062/Documents/GitHub/COSE212-2025fall/mini-fsharp/src/main/scala/kuplrg/Implementation.scala
text:
```scala
package kuplrg

object Implementation extends Template {

  import Expr.*, Value.*, Pattern.*

  // ---------------------------------------------------------------------------
  // Problem #1
  // ---------------------------------------------------------------------------
  def lookup(env: Env, x: String): Value = 
    env.get(x) match {
      case Some(v) => v
      case None => error("free identifier")
    }

  def tryMakeEnv(env: Env, p: Pattern, v: Value): Option[Env] = 
    (p, v) match {
      case (PId(x), _) => Some(env + (x -> v))
      case (PTuple(ps), TupleV(vs)) => 
        if (ps.length != vs.length) None
        else {
          ps.zip(vs).foldLeft(Some(env): Option[Env])((acc, pair) => 
            acc match {
              case None => None
              case Some(e) => tryMakeEnv(e, pair._1, pair._2)
            }
          )
        }
      case (PNil, ListV(Nil)) => Some(env)
      case (PCons(p1, p2), ListV(v1 :: v2s)) => 
        tryMakeEnv(env, p1, v1).flatMap { env1 =>
          tryMakeEnv(env1, p2, ListV(v2s))
        }
      case (PNum(n1), NumV(n2)) => 
        if (n1 == n2) Some(env) else None
      case (PBool(b1), BoolV(b2)) => 
        if (b1 == b2) Some(env) else None
      case (PNone, NoneV) => Some(env)
      case (PSome(p1), SomeV(v1)) => tryMakeEnv(env, p1, v1)
      case _ => None
    }
  
  def interp(expr: Expr, env: Env): Value = 
    expr match {
      case ENum(n) => NumV(n)
      case EBool(b) => BoolV(b)
      case EId(x) => lookup(env, x)

      case ENeg(e) => 
        interp(e, env) match {
          case NumV(n) => NumV(-n)
          case _ => error("invalid operation")
        }
      case EAdd(e1, e2) => 
        (interp(e1, env), interp(e2, env)) match {
          case (NumV(n1), NumV(n2)) => NumV(n1 + n2)
          case _ => error("invalid operation")
        }
      case EMul(e1, e2) => 
        (interp(e1, env), interp(e2, env)) match {
          case (NumV(n1), NumV(n2)) => NumV(n1 * n2)
          case _ => error("invalid operation")
        }
      case EDiv(e1, e2) => 
        (interp(e1, env), interp(e2, env)) match {
          case (_, NumV(0)) => error("invalid operation")
          case (NumV(n1), NumV(n2)) => NumV(n1 / n2)
          case _ => error("invalid operation")
        }
      case EMod(e1, e2) => 
        (interp(e1, env), interp(e2, env)) match {
          case (_, NumV(0)) => error("invalid operation")
          case (NumV(n1), NumV(n2)) => NumV(n1 % n2)
          case _ => error("invalid operation")
        }

      case EEq(e1, e2) => 
        BoolV(interp(@@e1, env) == interp(e2, env))
      case ELt(e1, e2) =>
        (interp(e1, env), interp(e2, env)) match {
          case (NumV(n1), NumV(n2)) => BoolV(n1 < n2)
          case _ => error("invalid operation")
        }
      case EIf(e1, e2, e3) =>
        interp(e1, env) match {
          case BoolV(b) => if (b) interp(e2, env) else interp(e3, env)
          case _ => error("not a boolean")
        }

      case ENil => ListV(Nil)
      case ECons(e1, e2) =>
        val v1 = interp(e1, env)
        interp(e2, env) match {
          case ListV(vs) => ListV(v1 :: vs)
          case _ => error("not a list")
        }
      case ETuple(es) =>
        TupleV(es.map(e => interp(e, env)))

      case ENone => NoneV
      case ESome(e) => SomeV(interp(e, env))

      case ELet(p, v, s) =>
        val value = interp(v, env)
        val newEnv = tryMakeEnv(env, p, value)
        newEnv match {
          case Some(e) => interp(s, e)
          case None => error("invalid pattern match")
        }

      // fs: List[NamedFun], NamedFun(name: String, param: Pattern, body: Expr)
      case ERec(fs, s) =>
        lazy val funBindings: List[(String, Value)] = fs.map { f =>
          (f.name, CloV(f.param, f.body, () => funBindings.toMap ++ env))
        }
        val newEnv: Env = funBindings.toMap ++ env
        interp(s, newEnv)
      case EFun(p, b) => CloV(p, b, () => env)
      case EApp(f, a) =>
        interp(f, env) match {
          case CloV(p, b, getClosureEnv) => 
            val argValue = interp(a, env)
            val closureEnv = getClosureEnv()
            val newEnv = tryMakeEnv(closureEnv, p, argValue)
            newEnv match {
              case Some(e) => interp(b, e)
              case None => error("invalid pattern match")
            }
          case _ => error("not a function")
        }
        
      // EMatch(e: Expr, cs: List[Case]), Case(pattern: Pattern, body: Expr)
      case EMatch(e, cs) =>
        val v = interp(e, env)
        def tryMatch(cases: List[Case]): Value = 
          cases match {
            case Nil => error("unmatched value")
            case Case(p: Pattern, b: Expr) :: rest => 
              tryMakeEnv(env, p, v) match {
                case Some(newEnv) => interp(b, newEnv)
                case None => tryMatch(rest)
              }
          }
        tryMatch(cs)
    }

  // ---------------------------------------------------------------------------
  // Problem #2
  // ---------------------------------------------------------------------------
  def hanoiMovesBody: String = """
    let rec append l1 l2 =
        match l1 with
 [] -> l2
 h :: t -> (h :: (append t l2))
    in
    let rec innerHanoiMoves n source temp target =
        if n = 0 then
            []
        else
            let m1 = innerHanoiMoves (n - 1) source target temp in
            let move = (source, target) :: [] in
            let m2 = innerHanoiMoves (n - 1) temp source target in
            append m1 (append move m2)
    in
    innerHanoiMoves n source temp target
  """
}

```


#### Short summary: 

empty definition using pc, found symbol in pc: `<none>`.