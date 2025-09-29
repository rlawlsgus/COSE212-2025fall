package kuplrg

import scala.util.parsing.combinator.*

// expressions
enum Expr {
  // numbers
  case ENum(number: BigInt)
  // booleans
  case EBool(bool: Boolean)
  // identifier lookups
  case EId(name: String)
  // negation
  case ENeg(expr: Expr)
  // addition
  case EAdd(left: Expr, right: Expr)
  // multiplication
  case EMul(left: Expr, right: Expr)
  // division
  case EDiv(left: Expr, right: Expr)
  // modulo
  case EMod(left: Expr, right: Expr)
  // equal-to
  case EEq(left: Expr, right: Expr)
  // less-than
  case ELt(left: Expr, right: Expr)
  // conditional
  case EIf(cond: Expr, thenExpr: Expr, elseExpr: Expr)
  // empty list
  case ENil
  // list cons
  case ECons(head: Expr, tail: Expr)
  // tuple
  case ETuple(exprs: List[Expr])
  // none
  case ENone
  // some
  case ESome(value: Expr)
  // let binding
  case ELet(pattern: Pattern, value: Expr, scope: Expr)
  // mutually recursive function
  case ERec(funs: List[NamedFun], scope: Expr)
  // lambda function
  case EFun(param: Pattern, body: Expr)
  // function application
  case EApp(fun: Expr, args: Expr)
  // pattern matching
  case EMatch(value: Expr, cases: List[Case])

  // the string form of an expression
  def str: String = this match
    case ListStr(s) => s"[$s]"
    case _          => rawStr

  // the raw string form of an expression
  def rawStr: String = this match
    case ENum(n)           => n.toString
    case EBool(b)          => b.toString
    case EId(x)            => x
    case ENeg(e)           => s"-(${e.str})"
    case EAdd(l, r)        => s"(${l.str} + ${r.str})"
    case EMul(l, r)        => s"(${l.str} * ${r.str})"
    case EDiv(l, r)        => s"(${l.str} / ${r.str})"
    case EMod(l, r)        => s"(${l.str} % ${r.str})"
    case EEq(l, r)         => s"(${l.str} = ${r.str})"
    case ELt(l, r)         => s"(${l.str} < ${r.str})"
    case EIf(c, t, e: EIf) => s"if ${c.str} then ${t.str} el${e.str}"
    case EIf(c, t, e)      => s"if ${c.str} then ${t.str} else ${e.str}"
    case ENil              => "[]"
    case ECons(h, t)       => s"(${h.str} :: ${t.str})"
    case ETuple(es)        => s"(${es.map(_.str).mkString(", ")})"
    case ENone             => s"None"
    case ESome(v)          => s"(Some ${v.str})"
    case ELet(p, v, s)     => s"let ${p.str} ${s.getBodyStr("=")} in ${s.str})"
    case ERec(fs, s) =>
      s"let rec ${fs.map(_.str).mkString(" and ")} in ${s.str}"
    case EFun(p, b)    => s"fun ${p.str} ${b.getBodyStr("->")}"
    case EApp(f, a)    => s"${f.str} ${a.str}"
    case EMatch(v, cs) => s"match ${v.str} with ${cs.map(_.str).mkString(" ")}"

  def getBodyStr(op: String): String = this match
    case EFun(p, b) => s"${p.str} ${b.getBodyStr(op)}"
    case _          => s"$op ${this.str}"
}

// patterns
enum Pattern {
  case PNum(number: BigInt)
  case PBool(bool: Boolean)
  case PId(name: String)
  case PNil
  case PCons(head: Pattern, tail: Pattern)
  case PTuple(patterns: List[Pattern])
  case PNone
  case PSome(pattern: Pattern)

  // the string form of an expression
  def str: String = this match
    case ListStr(s) => s"[$s]"
    case _          => rawStr

  // the raw string form of an expression
  def rawStr: String = this match
    case PNum(n)     => n.toString
    case PBool(b)    => b.toString
    case PId(x)      => x
    case PNil        => "[]"
    case PCons(h, t) => s"(${h.str} :: ${t.str})"
    case PTuple(ps)  => s"(${ps.map(_.str).mkString(", ")})"
    case PNone       => "None"
    case PSome(p)    => s"(Some ${p.str})"
}

// named functions
case class NamedFun(name: String, param: Pattern, body: Expr):
  // the string form of a named function
  def str: String = s"$name ${param.str} ${body.getBodyStr("=")}"

// cases
case class Case(pattern: Pattern, body: Expr):
  // the string form of a case
  def str: String = s"| ${pattern.str} ${body.getBodyStr("->")}"

// environments
type Env = Map[String, Value]

// values
enum Value {
  // number value
  case NumV(number: BigInt)
  // boolean value
  case BoolV(bool: Boolean)
  // empty list value
  case ListV(elements: List[Value])
  // tuple value
  case TupleV(values: List[Value])
  // none value
  case NoneV
  // some value
  case SomeV(value: Value)
  // closure value
  case CloV(pattern: Pattern, body: Expr, env: () => Env)

  // the string form of a value
  def str: String = this match
    case NumV(n)       => n.toString
    case BoolV(b)      => b.toString
    case ListV(vs)     => s"[${vs.map(_.str).mkString("; ")}]"
    case TupleV(vs)    => s"(${vs.map(_.str).mkString(", ")})"
    case NoneV         => "None"
    case SomeV(v)      => s"(Some ${v.str})"
    case CloV(p, b, e) => "<function>"
}

// -----------------------------------------------------------------------------
// Parsers
// -----------------------------------------------------------------------------
object Expr extends Parser.From(Parser.expr)
object Parser extends RegexParsers with PackratParsers {
  import Expr.*, Pattern.*
  type P[+T] = PackratParser[T]
  class From[T](p: Parser[T]) {
    def apply(s: String): T = parseAll(p, s).getOrElse(error("parse error"))
  }
  private val keywords = Set(
    "and",
    "elif",
    "else",
    "false",
    "fun",
    "if",
    "in",
    "let",
    "match",
    "rec",
    "then",
    "true",
    "with",
  )
  private val d: String = "0-9"
  private val w: String = "_a-zA-Z"
  private lazy val idx: P[Int] = "_[1-9][0-9]*".r ^^ (_.tail.toInt)
  private lazy val num: P[BigInt] = s"[$d]+".r ^^ BigInt.apply
  private lazy val bool: P[Boolean] = "true" ^^^ true | "false" ^^^ false
  private lazy val id: P[String] = s"[$w][$w$d]*".r.withFilter(!keywords(_))
  lazy val expr: P[Expr] = {
    lazy val e0: P[Expr] = rep1sep(e1, ",") ^^ {
      case List(e) => e
      case es      => ETuple(es)
    }
    lazy val e1: P[Expr] = rep1sep(e2, "||") ^^ (_.reduceLeft(EOr))
    lazy val e2: P[Expr] = rep1sep(e3, "&&") ^^ (_.reduceLeft(EAnd))
    lazy val e3: P[Expr] = e4 ~ rep(("=" | "<>") ~ e4) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "=" ~ r) => EEq(l, r)
          case (l, _ ~ r)   => ENe(l, r)
        }
    }
    lazy val e4: P[Expr] = e5 ~ rep(("<=" | "<" | ">=" | ">") ~ e5) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "<" ~ r)  => ELt(l, r)
          case (l, "<=" ~ r) => ELe(l, r)
          case (l, ">" ~ r)  => EGt(l, r)
          case (l, _ ~ r)    => EGe(l, r)
        }
    }
    lazy val e5: P[Expr] = rep1sep(e6, "::") ^^ (_.reduceRight(ECons.apply))
    lazy val e6: P[Expr] = e7 ~ rep(("+" | "-") ~ e7) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "+" ~ r) => EAdd(l, r)
          case (l, _ ~ r)   => ESub(l, r)
        }
    }
    lazy val e7: P[Expr] = e8 ~ rep(("*" | "/" | "%") ~ e8) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "*" ~ r) => EMul(l, r)
          case (l, "/" ~ r) => EDiv(l, r)
          case (l, _ ~ r)   => EMod(l, r)
        }
    }
    lazy val e8: P[Expr] = "-" ~> e8 ^^ ENeg.apply | "!" ~> e8 ^^ ENot | e9
    lazy val e9: P[Expr] = rep1(e10) ^^ { _.reduceLeft(EApp.apply) }
    lazy val e10: P[Expr] = {
      "fun" ~> pattern ~ curry("->") ^^ {
        case p ~ b => EFun(p, b)
      } | "let" ~ "rec" ~> rep1sep(namedFun, "and") ~ ("in" ~> e0) ^^ {
        case fs ~ b => ERec(fs, b)
      } | "let" ~> pattern ~ ("=" ~> e0) ~ ("in" ~> e0) ^^ {
        case p ~ e ~ b => ELet(p, e, b)
      } | "let" ~> id ~ curry("=") ~ ("in" ~> e0) ^^ {
        case x ~ e ~ b => ELet(PId(x), e, b)
      } | "if" ~> e0 ~ ("then" ~> e0) ~ rep(
        "elif" ~> e0 ~ ("then" ~> e0),
      ) ~ ("else" ~> e0) ^^ {
        case c ~ t ~ is ~ e =>
          EIf(c, t, is.foldRight(e) { case (c ~ t, e) => EIf(c, t, e) })
      } | "match" ~> e0 ~ ("with" ~> rep1("|" ~> pattern ~ ("->" ~> e0))) ^^ {
        case v ~ cs => EMatch(v, cs.map { case p ~ b => Case(p, b) })
      } | "None" ^^^ ENone | "Some" ~> e11 ^^ ESome.apply | e11
    }
    lazy val e11: P[Expr] = {
      "(" ~ ")" ^^^ ETuple(Nil) |
      "(" ~> e0 <~ ")" |
      num ^^ ENum.apply |
      bool ^^ EBool.apply |
      "[" ~> repsep(e0, ";") <~ "]" ^^ EList |
      id ^^ EId.apply
    }
    e0
  }

  // patterns
  private lazy val pattern: P[Pattern] = {
    lazy val p0: P[Pattern] = rep1sep(p1, ",") ^^ {
      case List(p) => p
      case ps      => PTuple(ps)
    }
    lazy val p1: P[Pattern] = rep1sep(p2, "::") ^^ (_.reduceRight(PCons.apply))
    lazy val p2: P[Pattern] = "Some" ~> p3 ^^ PSome.apply | p3
    lazy val p3: P[Pattern] = {
      "(" ~ ")" ^^^ PTuple(Nil) |
      "(" ~> p0 <~ ")" |
      "[" ~> repsep(p0, ";") <~ "]" ^^ { _.foldRight(PNil)(PCons.apply) } |
      num ^^ PNum.apply |
      bool ^^ PBool.apply |
      "None" ^^^ PNone |
      "Nil" ^^^ PNil |
      id ^^ PId.apply
    }
    p0
  }

  // named functions
  private lazy val namedFun: P[NamedFun] =
    id ~ pattern ~ curry("=") ^^ { case n ~ p ~ b => NamedFun(n, p, b) }

  // let bindings
  private def curry(sep: String): P[Expr] = (rep(pattern) <~ sep) ~ expr ^^ {
    case ps ~ v => ps.foldRight(v)(EFun.apply)
  }

  // desugaring rules
  private val T: Expr = EBool(true)
  private val F: Expr = EBool(false)
  private def ESub(left: Expr, right: Expr): Expr = EAdd(left, ENeg(right))
  private def EAnd(left: Expr, right: Expr): Expr = EIf(left, right, F)
  private def EOr(left: Expr, right: Expr): Expr = EIf(left, T, right)
  private def ENot(expr: Expr): Expr = EIf(expr, F, T)
  private def ENe(left: Expr, right: Expr): Expr = ENot(EEq(left, right))
  private def ELe(left: Expr, right: Expr): Expr =
    EOr(ELt(left, right), EEq(left, right))
  private def EGt(left: Expr, right: Expr): Expr = ENot(ELe(left, right))
  private def EGe(left: Expr, right: Expr): Expr = ENot(ELt(left, right))
  private def EList(exprs: List[Expr]): Expr =
    exprs.foldRight(ENil: Expr)(ECons.apply)
}

// the list string form of an expression
private object ListStr {
  import Expr.*, Pattern.*
  def unapply(expr: Expr): Option[String] = expr match
    case ENil                 => Some("")
    case ECons(h, ENil)       => Some(h.str)
    case ECons(h, ListStr(t)) => Some(s"${h.str}; $t")
    case _                    => None
  def unapply(pattern: Pattern): Option[String] = pattern match
    case PNil                 => Some("")
    case PCons(h, PNil)       => Some(h.str)
    case PCons(h, ListStr(t)) => Some(s"${h.str}; $t")
    case _                    => None
}
