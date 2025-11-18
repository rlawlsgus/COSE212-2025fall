package kuplrg

import scala.util.parsing.combinator.*

// programs
case class Program(stmts: List[Stmt], expr: Expr):
  // the string form of a program
  def str: String = stmts.map(_.str(0) + newline(0)).mkString + expr.str

// statements
enum Stmt:
  // pass
  case SPass
  // expression statement
  case SExpr(expr: Expr)
  // variable assignment
  case SAssign(name: String, expr: Expr)
  // set item
  case SSetItem(base: Expr, idx: Expr, expr: Expr)
  // if-else
  case SIf(cond: Expr, thenBlock: Block, elseBlock: Block)
  // while loop
  case SWhile(cond: Expr, body: Block)
  // break
  case SBreak
  // continue
  case SContinue
  // try-except
  case STry(body: Block, except: Block)
  // raise
  case SRaise
  // function definition
  case SDef(name: String, params: List[String], body: Block)
  // return
  case SReturn(expr: Expr)
  // yield
  case SYield(expr: Expr)

  // the string form of a statement
  def str: String = this match
    case SPass             => "pass"
    case SExpr(e)          => e.str
    case SAssign(x, e)     => s"$x = ${e.str}"
    case SSetItem(b, i, e) => s"${b.str}[${i.str}] = ${e.str}"
    case SIf(c, t, e)      => s"if ${c.str}: ... else: ..."
    case SWhile(e, b)      => s"while ${e.str}: ..."
    case SBreak            => "break"
    case SContinue         => "continue"
    case STry(b, e)        => s"try: ... except: ..."
    case SRaise            => "raise"
    case SDef(x, ps, b)    => s"def $x(${ps.mkString(", ")}): ..."
    case SReturn(e)        => s"return ${e.str}"
    case SYield(e)         => s"yield ${e.str}"

  // the string form of a statement
  def str(depth: Int): String = this match
    case SDef(x, ps, b) =>
      s"def $x(${ps.mkString(", ")}):${b.str(depth)}"
    case SIf(c, t, e) =>
      s"if ${c.str}:${t.str(depth)}${newline(depth)}else:${e.str(depth)}"
    case STry(b, e) =>
      s"try:${b.str(depth)}${newline(depth)}except:${e.str(depth)}"
    case SWhile(e, b) => s"while ${e.str}:${b.str(depth)}"
    case _            => str

// blocks
case class Block(stmts: List[Stmt]):
  // the string form of a block
  def str(depth: Int): String =
    if (stmts.isEmpty) s"${newline(depth + 1)}pass"
    else stmts.map(newline(depth + 1) + _.str(depth + 1)).mkString
object Block { def apply(stmts: Stmt*): Block = Block(stmts.toList) }

// expressions
enum Expr:
  // none
  case ENone
  // number
  case ENum(number: BigInt)
  // boolean
  case EBool(bool: Boolean)
  // identifier lookup
  case EId(name: String)
  // binary operation
  case EBOp(bop: BOp, left: Expr, right: Expr)
  // list
  case EList(elements: List[Expr])
  // append
  case EAppend(list: Expr, elem: Expr)
  // get item
  case EGetItem(list: Expr, idx: Expr)
  // lambda function
  case ELambda(params: List[String], body: Expr)
  // function application
  case EApp(fun: Expr, args: List[Expr])
  // conditional expression
  case ECond(cond: Expr, thenExpr: Expr, elseExpr: Expr)
  // iterator
  case EIter(expr: Expr)
  // next item from iterator
  case ENext(expr: Expr)

  // the string form of an expression
  def str: String = this match
    case ENone          => "None"
    case ENum(n)        => n.toString
    case EBool(b)       => if (b) "True" else "False"
    case EId(x)         => x
    case EBOp(op, l, r) => s"(${l.str} ${op.str} ${r.str})"
    case EList(es)      => s"[${es.map(_.str).mkString(", ")}]"
    case EAppend(l, e)  => s"${l.str}.append(${e.str})"
    case EGetItem(l, i) => s"${l.str}[${i.str}]"
    case ELambda(ps, b) => s"(lambda ${ps.mkString(", ")}: ${b.str})"
    case EApp(f, es)    => s"${f.str}(${es.map(_.str).mkString(", ")})"
    case ECond(c, t, e) => s"(${t.str} if ${c.str} else ${e.str})"
    case EIter(e)       => s"iter(${e.str})"
    case ENext(e)       => s"next(${e.str})"

import Expr.*

// states
case class State(cont: Cont, stack: Stack, handler: Handler, mem: Mem):
  // string form of a state
  def str: String =
    val memList = mem.toList.sortBy(_._1)
    val hdlList = handler.toList.sortBy(_._1.str)
    getEnv.fold("") { env =>
      s"* env    : ${env.toList
        .sortBy(_._1)
        .map((k, a) => s"\n  - $k : #$a")
        .mkString}\n"
    } + s"""
    |* cont   : ${(cont.map(_.str) :+ "[]").mkString(" :: ")}
    |* stack  : ${(stack.map(_.str) :+ "[]").mkString(" :: ")}
    |* handler: ${hdlList
      .map((c, kv) =>
        s"\n  - ${c.str} -> ${(kv.cont.map(_.str) :+ "[]").mkString(" :: ")}",
      )
      .mkString}
    |* mem    : [${memList.map((k, v) => s"#$k -> ${v.str}").mkString(", ")}]
    """.trim.stripMargin

  import Inst.*
  def getEnv: Option[Env] = for {
    inst <- cont.headOption
    env <- inst match
      case IBlock(env, _) => Some(env)
      case IStmt(env, _)  => Some(env)
      case IExpr(env, _)  => Some(env)
      case _              => None
  } yield env

// continuations
type Cont = List[Inst]

// instructions
enum Inst:
  // block evaluation
  case IBlock(env: Env, block: Block)
  // statement evaluation
  case IStmt(env: Env, stmt: Stmt)
  // expression evaluation
  case IExpr(env: Env, expr: Expr)
  // binary operation
  case IBOp(bop: BOp)
  // address write
  case IWrite(addr: Addr)
  // get item
  case IGetItem
  // set item
  case ISetItem
  // list allocation
  case IList(length: Int)
  // append to list
  case IAppend
  // conditional jump
  case IJmpIf(kv: KValue)
  // unconditional jump
  case IJmp(control: Control)
  // raise
  case IRaise(error: Error)
  // function call
  case ICall(argSize: Int)
  // return
  case IReturn
  // yield
  case IYield
  // iterator
  case IIter
  // next iterator item
  case INext
  // drop
  case IDrop

  // the string form of a continuation
  def str: String = this match
    case IBlock(_, b) => s"eval[<env> |- <block>]"
    case IStmt(_, s)  => s"eval[<env> |- ${s.str}]"
    case IExpr(_, e)  => s"eval[<env> |- ${e.str}]"
    case IBOp(op)     => s"(${op.str})"
    case IWrite(a)    => s"write[#$a]"
    case IGetItem     => s"get-item"
    case ISetItem     => s"set-item"
    case IList(n)     => s"list[$n]"
    case IAppend      => s"append"
    case IJmpIf(_)    => s"jmp-if[_]"
    case IJmp(c)      => s"jmp[${c.str}]"
    case IRaise(msg)  => s"raise[$msg]"
    case ICall(n)     => s"call[$n]"
    case IReturn      => s"return"
    case IYield       => s"yield"
    case IIter        => s"iter"
    case INext        => s"next"
    case IDrop        => s"drop"

// binary operations
enum BOp:
  // addition
  case Add
  // multiplication
  case Mul
  // division
  case Div
  // modulo
  case Mod
  // less-than
  case Lt
  // less-than or equal-to
  case Lte
  // value-based equality
  case Eq
  // address-based equality
  case Is

  // the string form of a binary operation
  def str: String = this match
    case Add => "+"
    case Mul => "*"
    case Div => "//"
    case Mod => "%"
    case Lt  => "<"
    case Lte => "<="
    case Eq  => "=="
    case Is  => "is"

enum Error:
  case RuntimeError
  case ZeroDivisionError
  case TypeError
  case IndexError
  case StopIteration
  case NameError(name: String)

  // the string form of an error
  def str: String = this match
    case RuntimeError      => "RuntimeError"
    case ZeroDivisionError => "ZeroDivisionError"
    case TypeError         => "TypeError"
    case IndexError        => "IndexError"
    case StopIteration     => "StopIteration"
    case NameError(x)      => s"NameError: $x"

// value stacks
type Stack = List[Value]

// values
enum Value:
  // none value
  case NoneV
  // number value
  case NumV(number: BigInt)
  // boolean value
  case BoolV(bool: Boolean)
  // address value
  case AddrV(addr: Addr)
  // list value
  case ListV(elements: List[Value])
  // closure value
  case CloV(params: List[String], body: Block, env: Env)
  // generator value
  case GenV(params: List[String], body: Block, env: Env)
  // continuation value
  case ContV(pair: KValue)
  // iterator value
  case IterV(target: Addr, idx: Int)

  // the simple string form of a value
  def str: String = this match
    case NoneV          => "None"
    case NumV(n)        => n.toString
    case BoolV(b)       => if (b) "True" else "False"
    case AddrV(a)       => s"#$a"
    case ListV(es)      => s"[${es.map(_.str).mkString(", ")}]"
    case CloV(ps, _, _) => s"<clo ${ps.mkString(", ")}: ...>"
    case GenV(ps, _, _) => s"<gen ${ps.mkString(", ")}: ...>"
    case ContV(_)       => s"<cont>"
    case IterV(a, i)    => s"<iter>(#$a, $i)"

  // the string form of a value with memory
  def str(mem: Mem): String = this match
    case AddrV(a)      => mem.get(a).fold(s"<dangling address>")(_.str(mem))
    case ListV(es)     => s"[${es.map(_.str(mem)).mkString(", ")}]"
    case CloV(_, _, _) => s"<clo>"
    case GenV(_, _, _) => s"<gen>"
    case IterV(_, _)   => s"<iter>"
    case _             => str

// control handlers
type Handler = Map[Control, KValue]

// controls
enum Control:
  case Return
  case Break
  case Continue
  case Raise
  case Finally
  case Yield

  // the string form of a control
  def str: String = this match
    case Return   => "return"
    case Break    => "break"
    case Continue => "continue"
    case Raise    => "raise"
    case Finally  => "finally"
    case Yield    => "yield"

// continuation values
case class KValue(cont: Cont, stack: Stack, handler: Handler)

// memories
type Mem = Map[Addr, Value]

// environments
type Env = Map[String, Addr]

// addresses
type Addr = Int

// -----------------------------------------------------------------------------
// Parsers
// -----------------------------------------------------------------------------
object Program extends Parser.From(Parser.program)
object Parser extends RegexParsers with PackratParsers {
  import Stmt.*, Expr.*, BOp.*
  type P[+T] = PackratParser[T]
  class From[T](p: Parser[T]) {
    def apply(s: String): T = parseAll(p, s) match
      case Success(x, _) => x
      case res: NoSuccess =>
        val pos = res.next.pos
        syntaxError(s"parse failure at $pos\n${pos.longString}")
  }
  private val keywords = Set(
    "False",
    "None",
    "True",
    "and",
    "break",
    "continue",
    "def",
    "elif",
    "else",
    "except",
    "for",
    "from",
    "if",
    "in",
    "lambda",
    "not",
    "or",
    "pass",
    "raise",
    "return",
    "try",
    "while",
    "yield",
  )
  private val d: String = "0-9"
  private val w: String = "_a-zA-Z"
  private lazy val num: P[BigInt] = s"-?[$d]+".r ^^ BigInt.apply
  private lazy val bool: P[Boolean] = "True" ^^^ true | "False" ^^^ false
  private lazy val id: P[String] = s"[$w][$w$d]*".r.withFilter(!keywords(_))
  lazy val program: P[Program] =
    s"(\r?\n)*".r ~>
    phrase(repsep(stmts(0), linesep(0)) ^^ { _.flatten }).flatMap {
      case ss :+ SExpr(e) => success(mustValid(Program(ss, e)))
      case ss =>
        mustValid(Context(), ss)
        syntaxError("A program must end with an expression")
    }
  def stmts(depth: Int): P[List[Stmt]] = compoundStmt(depth) | simpleStmts
  def compoundStmt(depth: Int): P[List[Stmt]] = {
    "def" ~> id ~ ("(" ~> params <~ ")") ~ (":" ~> block(depth)) ^^ {
      case n ~ ps ~ b => List(SDef(n, ps, b))
    } |
    "if" ~> expr ~ (":" ~> block(depth)) ~ rep(
      linesep(depth) ~ "elif" ~> expr ~ (":" ~> block(depth)),
    ) ~ opt(linesep(depth) ~ "else" ~> (":" ~> block(depth))) ^^ {
      case c ~ t ~ is ~ e =>
        val e0 = e.getOrElse(Block(SPass))
        val e1 = is.foldRight(e0) { case (c ~ t, e) => Block(SIf(c, t, e)) }
        List(SIf(c, t, e1))
    } |
    "for" ~> (id <~ "in") ~ expr ~ (":" ~> block(depth)) ^^ {
      case x ~ e ~ b => SFor(x, e, b)
    } |
    "try" ~> (":" ~> block(depth)) ~
    (linesep(depth) ~ "except" ~ ":" ~> block(depth)) ^^ {
      case b ~ e => List(STry(b, e))
    } |
    "while" ~> expr ~ (":" ~> block(depth)) ^^ {
      case c ~ b => List(SWhile(c, b))
    }
  }
  lazy val simpleStmts: P[List[Stmt]] =
    rep1sep(simpleStmt, ";") <~ opt(";") ^^ { _.flatten }
  lazy val simpleStmt: P[List[Stmt]] = {
    val target =
      atom ~ rep("[" ~> expr <~ "]" ~ guard("[")) ~ ("[" ~> expr <~ "]") ^^ {
        case x ~ ys ~ z => ys.foldLeft(x)(EGetItem(_, _)) -> z
      }
    id ~ ("=" ~> expr) ^^ { case x ~ e => List(SAssign(x, e)) } |
    target ~ ("=" ~> expr) ^^ { case (l, i) ~ e => List(SSetItem(l, i, e)) } |
    "return" ~> expr ^^ { e => List(SReturn(e)) } |
    "return" ^^^ List(SReturn(ENone)) |
    "raise" ^^^ List(SRaise) |
    "pass" ^^^ List(SPass) |
    "yield from" ~> expr ^^ { SYieldFrom(_) } |
    "yield" ~> opt(expr) ^^ { e => List(SYield(e.getOrElse(ENone))) } |
    "break" ^^^ List(SBreak) |
    "continue" ^^^ List(SContinue) |
    expr ^^ { e => List(SExpr(e)) }
  }
  lazy val expr: P[Expr] = {
    lazy val e0: P[Expr] = "lambda" ~> params ~ (":" ~> e0) ^^ {
      case ps ~ b => ELambda(ps, b)
    } | e1 ~ ("if" ~> e1) ~ ("else" ~> e0) ^^ {
      case t ~ c ~ e => ECond(c, t, e)
    } | e1
    lazy val e1: P[Expr] = e2 ~ rep("or" ~> e2) ^^ {
      case e ~ es => es.foldLeft(e)(EOr)
    }
    lazy val e2: P[Expr] = e3 ~ rep("and" ~> e3) ^^ {
      case e ~ es => es.foldLeft(e)(EAnd)
    }
    lazy val e3: P[Expr] = "not" ~> e3 ^^ ENot.apply | e4
    lazy val e4: P[Expr] = e5 ~ rep(
      ("==" | "!=" | "<=" | "<" | ">=" | ">" | "is not" | "is") ~ e5,
    ) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "==" ~ r) => EEq(l, r)
          case (l, "!=" ~ r) => ENeq(l, r)
          case (l, "<" ~ r)  => ELt(l, r)
          case (l, "<=" ~ r) => ELte(l, r)
          case (l, ">" ~ r)  => EGt(l, r)
          case (l, ">=" ~ r) => EGte(l, r)
          case (l, "is" ~ r) => EIs(l, r)
          case (l, _ ~ r)    => EIsNot(l, r)
        }
    }
    lazy val e5: P[Expr] = e6 ~ rep(("+" | "-") ~ e6) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "+" ~ r) => EAdd(l, r)
          case (l, _ ~ r)   => ESub(l, r)
        }
    }
    lazy val e6: P[Expr] = e7 ~ rep(("*" | "//" | "%") ~ e7) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "*" ~ r)  => EMul(l, r)
          case (l, "//" ~ r) => EDiv(l, r)
          case (l, _ ~ r)    => EMod(l, r)
        }
    }
    lazy val e7: P[Expr] = "-" ~> e7 ^^ ENeg | e8
    import PostfixOps.*
    lazy val e8: P[Expr] = atom ~ rep(
      "." ~ "append" ~> "(" ~> expr <~ ")" ^^ PAppend.apply |
      "(" ~> repsep(e0, ",") <~ ")" ^^ PApp.apply |
      "[" ~> e0 <~ "]" ^^ PGetItem.apply,
    ) ^^ {
      case e ~ ops =>
        ops.foldLeft(e) {
          case (l, PAppend(r))  => EAppend(l, r)
          case (f, PApp(es))    => EApp(f, es)
          case (l, PGetItem(s)) => EGetItem(l, s)
        }
    }
    e0
  }
  lazy val atom: P[Expr] = {
    "None" ^^^ ENone |
    num ^^ ENum.apply |
    bool ^^ EBool.apply |
    "iter" ~ "(" ~> expr <~ ")" ^^ EIter.apply |
    "next" ~ "(" ~> expr <~ ")" ^^ ENext.apply |
    id ^^ EId.apply |
    "(" ~> expr <~ ")" |
    "[" ~> repsep(expr, ",") <~ "]" ^^ EList.apply
  }
  lazy val params: P[List[String]] = repsep(id, ",") ^^ { mustValid(_) }
  def block(depth: Int): P[Block] =
    rep1 {
      linesep(depth + 1) ~> stmts(depth + 1)
    } ^^ { ss => Block(ss.flatten) } |
    simpleStmts ^^ { Block(_) }

  // postfix operators
  private enum PostfixOps:
    case PAppend(elem: Expr)
    case PApp(args: List[Expr])
    case PGetItem(idx: Expr)

  // desugaring rules
  private val T: Expr = EBool(true)
  private val F: Expr = EBool(false)
  private def EAdd(l: Expr, r: Expr): Expr = EBOp(Add, l, r)
  private def ESub(l: Expr, r: Expr): Expr = EAdd(l, ENeg(r))
  private def ENeg(e: Expr): Expr = EMul(e, ENum(-1))
  private def EMul(l: Expr, r: Expr): Expr = EBOp(Mul, l, r)
  private def EDiv(l: Expr, r: Expr): Expr = EBOp(Div, l, r)
  private def EMod(l: Expr, r: Expr): Expr = EBOp(Mod, l, r)
  private def ELt(l: Expr, r: Expr): Expr = EBOp(Lt, l, r)
  private def ELte(l: Expr, r: Expr): Expr = EBOp(Lte, l, r)
  private def EGt(l: Expr, r: Expr): Expr = ENot(ELte(l, r))
  private def EGte(l: Expr, r: Expr): Expr = ENot(ELt(l, r))
  private def EEq(l: Expr, r: Expr): Expr = EBOp(Eq, l, r)
  private def ENeq(l: Expr, r: Expr): Expr = ENot(EEq(l, r))
  private def EIs(l: Expr, r: Expr): Expr = EBOp(Is, l, r)
  private def EIsNot(l: Expr, r: Expr): Expr = ENot(EIs(l, r))
  private def EAnd(l: Expr, r: Expr): Expr = ECond(l, r, F)
  private def EOr(l: Expr, r: Expr): Expr = ECond(l, T, r)
  private def ENot(e: Expr): Expr = ECond(e, F, T)

  private def SFor(x: String, e: Expr, b: Block): List[Stmt] =
    val it = tid
    List(
      SAssign(it, EIter(e)),
      SWhile(
        T,
        Block(
          STry(
            Block(SAssign(x, ENext(EId(it)))),
            Block(SBreak),
          ) :: b.stmts,
        ),
      ),
    )
  private def SYieldFrom(e: Expr): List[Stmt] =
    val x = tid
    SFor(x, e, Block(SYield(EId(x))))

  private def init = tidCount = -1
  private var tidCount = -1
  private def tid: String = { tidCount += 1; s"%$tidCount" }

  override val whiteSpace = s"""( |#.*|\r?\n *(#.*)?$$)+""".r
  def linesep(depth: Int): P[String] =
    rep(s"\r?\n *".r ~ guard(s"\r?\n".r)) ~> s"\r?\n *".r.filter(s =>
      (s.length - 1) / INDENT.length == depth,
    )
}

val INDENT = "  "
val LS = System.getProperty("line.separator")
def newline(depth: Int): String = LS + (INDENT * depth)

import Stmt.*, Expr.*
case class Context(inFunc: Boolean = false, inLoop: Boolean = false)

// validity check
def syntaxError(msg: String): Nothing = error(s"SyntaxError: $msg")
def mustValid(p: Program): Program = { mustValid(Context(), p.stmts); p }
def mustValid(ctxt: Context, b: Block): Unit = mustValid(ctxt, b.stmts)
def mustValid(ctxt: Context, stmts: List[Stmt]): Unit =
  stmts.map(mustValid(ctxt, _))
def mustValid(ctxt: Context, stmt: Stmt): Unit = stmt match
  case SReturn(_) if !ctxt.inFunc =>
    syntaxError("'return' outside function")
  case SYield(_) if !ctxt.inFunc =>
    syntaxError("'yield' outside function")
  case SBreak | SContinue if !ctxt.inLoop =>
    syntaxError("'break' or 'continue' outside loop")
  case SDef(_, ps, b) => mustValid(Context(true, false), b)
  case SIf(_, t, e)   => mustValid(ctxt, t); mustValid(ctxt, e)
  case SWhile(_, b)   => mustValid(ctxt.copy(inLoop = true), b)
  case STry(b, e)     => mustValid(ctxt, b); mustValid(ctxt, e)
  case _              =>
def mustValid(params: List[String]): List[String] =
  val dup = params
    .groupBy(identity)
    .filter(_._2.size > 1)
    .keys
    .mkString(", ")
  if (dup.nonEmpty) syntaxError(s"duplicate parameter names: ${dup}")
  params
