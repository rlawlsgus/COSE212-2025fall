package kuplrg

import scala.util.parsing.combinator.*

// expressions
enum Expr:
  // unit
  case EUnit
  // numbers
  case ENum(number: BigInt)
  // booleans
  case EBool(bool: Boolean)
  // strings
  case EStr(string: String)
  // identifier lookups
  case EId(name: String)
  // addition
  case EAdd(left: Expr, right: Expr)
  // multiplication
  case EMul(left: Expr, right: Expr)
  // division
  case EDiv(left: Expr, right: Expr)
  // modulo
  case EMod(left: Expr, right: Expr)
  // string concatenation
  case EConcat(left: Expr, right: Expr)
  // equal-to
  case EEq(left: Expr, right: Expr)
  // less-than
  case ELt(left: Expr, right: Expr)
  // sequence
  case ESeq(left: Expr, right: Expr)
  // conditional
  case EIf(cond: Expr, thenExpr: Expr, elseExpr: Expr)
  // immutable variable definitions
  case EVal(x: String, tyOpt: Option[Type], expr: Expr, body: Expr)
  // anonymous (lambda) functions
  case EFun(params: List[Param], body: Expr)
  // function applications
  case EApp(fun: Expr, tys: List[Type], args: List[Expr])
  // mutually recursive definitions
  case ERecDefs(defs: List[RecDef], body: Expr)
  // pattern matching
  case EMatch(expr: Expr, mcases: List[MatchCase])
  // exit
  case EExit(expr: Expr)

  // the string form of an expression
  def str: String = this match
    case EUnit         => "()"
    case ENum(n)       => n.toString
    case EBool(b)      => b.toString
    case EStr(s)       => s"\"$s\""
    case EId(x)        => x
    case EAdd(l, r)    => s"(${l.str} + ${r.str})"
    case EMul(l, r)    => s"(${l.str} * ${r.str})"
    case EDiv(l, r)    => s"(${l.str} / ${r.str})"
    case EMod(l, r)    => s"(${l.str} % ${r.str})"
    case EConcat(l, r) => s"(${l.str} ++ ${r.str})"
    case EEq(l, r)     => s"(${l.str} == ${r.str})"
    case ELt(l, r)     => s"(${l.str} < ${r.str})"
    case ESeq(l, r)    => s"{ ${l.str}; ${r.str} }"
    case EIf(c, t, e)  => s"(if (${c.str}) ${t.str} else ${e.str})"
    case EVal(x, t, e, b) =>
      s"val ${x}${t.fold("")(ty => s": ${ty.str}")} = ${e.str}; ${b.str}"
    case EFun(ps, b) =>
      s"((${ps.map(_.str).mkString(", ")}) => ${b.str})"
    case EApp(f, ts, as) =>
      val tstr = if (ts.isEmpty) "" else ts.map(_.str).mkString("[", ", ", "]")
      s"${f.str}$tstr(${as.map(_.str).mkString(", ")})"
    case ERecDefs(ds, b) =>
      s"{ ${ds.map(_.str + "; ").mkString} ${b.str} }"
    case EMatch(e, cs) =>
      s"{ ${e.str} match { ${cs.map(_.str).mkString("; ")} } }"
    case EExit(expr) => s"exit(${expr.str})"

// recursive definitions
enum RecDef:
  // immutable lazy variable definition
  case LazyVal(
    name: String,
    ty: Type,
    init: Expr,
  )
  // recursive function
  case RecFun(
    name: String,
    tvars: List[String],
    params: List[Param],
    rty: Type,
    body: Expr,
  )
  // polymorphic algebraic data type
  case TypeDef(
    name: String,
    tvars: List[String],
    varts: List[Variant],
  )

  // the string form of an expression
  def str: String = this match
    case LazyVal(x, t, e) =>
      s"lazy val $x: ${t.str} = ${e.str}"
    case RecFun(x, tns, ps, rty, b) =>
      val tnStr = if (tns.isEmpty) "" else tns.mkString("[", ", ", "]")
      s"def $x$tnStr(${ps.map(_.str).mkString(", ")}): ${rty.str} = ${b.str}"
    case TypeDef(x, tns, vs) =>
      val tnStr = if (tns.isEmpty) "" else tns.mkString("[", ", ", "]")
      s"enum $x$tnStr { ${vs.map(_.str).mkString("; ")} }"

// parameter definition
case class Param(name: String, ty: Type):
  // the string form of a parameter
  def str: String = s"$name: ${ty.str}"

// variant definition
case class Variant(name: String, params: List[Param]):
  // the string form of a variant
  def str: String = s"case $name(${params.map(_.str).mkString(", ")})"

// match case
case class MatchCase(name: String, params: List[String], body: Expr):
  // the string form of a case
  def str: String = s"case $name(${params.mkString(", ")}) => ${body.str}"

// environments
type Env = Map[String, Value]

// values
enum Value:
  // unit values
  case UnitV
  // number values
  case NumV(number: BigInt)
  // boolean values
  case BoolV(bool: Boolean)
  // string values
  case StrV(string: String)
  // closure values
  case CloV(params: List[String], body: Expr, env: () => Env)
  // expression values
  case ExprV(expr: Expr, env: () => Env)
  // constructor values
  case ConstrV(name: String)
  // variant values
  case VariantV(name: String, values: List[Value])

  // the string form of a value
  def str: String = this match
    case UnitV           => "()"
    case NumV(n)         => n.toString
    case BoolV(b)        => b.toString
    case StrV(s)         => s"\"$s\""
    case CloV(_, _, _)   => "<function>"
    case ExprV(_, _)     => s"<expr>"
    case ConstrV(n)      => s"<constructor: $n>"
    case VariantV(n, vs) => s"$n(${vs.map(_.str).mkString(", ")})"

// type environments
case class TypeEnv(
  vars: Map[String, Type] = Map(),
  tys: Map[String, TypeInfo] = Map(),
) {
  import TypeInfo.*
  def addVar(pair: (String, Type)): TypeEnv =
    TypeEnv(vars + pair, tys)
  def addVars(pairs: Iterable[(String, Type)]): TypeEnv =
    TypeEnv(vars ++ pairs, tys)
  def addTypeVars(xs: List[String]): TypeEnv =
    TypeEnv(vars, tys ++ xs.map(_ -> TIVar))
  def addTypeName(x: String, xs: List[String], ws: List[Variant]): TypeEnv =
    TypeEnv(vars, tys + (x -> TIAdt(xs, ws.map(w => w.name -> w.params).toMap)))
  def str: String =
    "TypeEnv {" + "\n" +
    (for ((name, ty) <- vars) yield s"  $name: ${ty.str}" + "\n").mkString +
    (for ((name, info) <- tys) yield s"  $name${info.str}" + "\n").mkString +
    "}"
}

// type information
enum TypeInfo:
  // type variable
  case TIVar
  // algebraic data type
  case TIAdt(tvars: List[String], variants: Map[String, List[Param]])

  def str: String = this match
    case TIVar => ""
    case TIAdt(tns, vs) =>
      val tnStr = if (tns.isEmpty) "" else tns.mkString("[", ", ", "]")
      val vsStr = vs
        .map {
          case (vname, params) =>
            s"    case $vname(${params.map(_.str).mkString(", ")})"
        }
        .mkString("\n")
      s"$tnStr {\n$vsStr\n  }"

// types
enum Type:
  // bottom types
  case NothingT
  // top types
  case AnyT
  // unit types
  case UnitT
  // number types
  case NumT
  // boolean types
  case BoolT
  // string types
  case StrT
  // parameterized type identifiers
  case IdT(name: String, tys: List[Type] = Nil)
  // function (arrow) types
  case ArrowT(tvars: List[String], paramTys: List[Type], retTy: Type)

  // the string form of a type
  def str: String = this match
    case NothingT     => "Nothing"
    case AnyT         => "Any"
    case UnitT        => "Unit"
    case NumT         => "Number"
    case BoolT        => "Boolean"
    case StrT         => "String"
    case IdT(tn, Nil) => tn
    case IdT(tn, ts)  => s"$tn[${ts.map(_.str).mkString(", ")}]"
    case ArrowT(tns, ps, b) =>
      val psStr = ps match
        case List(p: ArrowT) => s"(${p.str})"
        case List(p)         => s"${p.str}"
        case _               => s"(${ps.map(_.str).mkString(", ")})"
      if (tns.isEmpty) s"$psStr => ${b.str}"
      else s"${tns.mkString("[", ", ", "]")}($psStr => ${b.str})"

// -----------------------------------------------------------------------------
// Parsers
// -----------------------------------------------------------------------------
object Expr extends Parser.From(Parser.expr)
object Parser extends RegexParsers with PackratParsers {
  import Expr.*
  import Type.*
  import RecDef.*
  type P[+T] = PackratParser[T]
  class From[T](p: Parser[T]) {
    def apply(s: String): T = parseAll(p, s).getOrElse(error("parse error"))
  }
  private val keywords = Set(
    "Any",
    "Boolean",
    "Nothing",
    "Number",
    "String",
    "Unit",
    "case",
    "def",
    "else",
    "exit",
    "enum",
    "false",
    "if",
    "lazy",
    "match",
    "true",
    "val",
  )
  private val d: String = "0-9"
  private val w: String = "_a-zA-Z"
  private lazy val num: P[BigInt] = s"-?[$d]+".r ^^ BigInt.apply
  private lazy val bool: P[Boolean] = "true" ^^^ true | "false" ^^^ false
  private lazy val str: P[String] = "\"[^\"]*\"".r ^^ { _.drop(1).dropRight(1) }
  private lazy val id: P[String] = s"[$w][$w$d]*".r.withFilter(!keywords(_))

  // expressions
  lazy val expr: P[Expr] =
    lazy val e0: P[Expr] =
      rep1(e1 <~ opt(";")) ^^ { _.reduceLeft(ESeq.apply) }
    lazy val e1: P[Expr] = rep1(recDef <~ opt(";")) ~ e2 ^^ {
      case ds ~ e =>
        dupCheck(
          ds.flatMap {
            case LazyVal(x, _, _)      => Some(x)
            case RecFun(x, _, _, _, _) => Some(x)
            case _                     => None
          },
          "identifier",
        )
        dupCheck(
          ds.flatMap {
            case TypeDef(x, _, _) => Some(x)
            case _                => None
          },
          "type name",
        )
        ERecDefs(ds, e)
    } | e2
    lazy val e2: P[Expr] =
      "val" ~> id ~ opt(":" ~> ty) ~ ("=" ~> e1) ~ (opt(";") ~> e0) ^^ {
        case x ~ t ~ e ~ b => EVal(x, t, e, b)
      } |
      "if" ~> ("(" ~> e0 <~ ")") ~ e0 ~ ("else" ~> e1) ^^ {
        case c ~ t ~ e => EIf(c, t, e)
      } |
      params ~ ("=>" ~> e1) ^^ {
        case ps ~ b => EFun(ps, b)
      } |
      e3 ~ rep("match" ~ "{" ~> rep1(mcase <~ opt(";")) <~ "}") ^^ {
        case e ~ cs => cs.foldLeft(e)(EMatch.apply)
      }
    lazy val e3: P[Expr] = rep1sep(e4, "||") ^^ (_.reduceLeft(EOr))
    lazy val e4: P[Expr] = rep1sep(e5, "&&") ^^ (_.reduceLeft(EAnd))
    lazy val e5: P[Expr] = e6 ~ rep(("==" | "!=") ~ e5) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "==" ~ r) => EEq(l, r)
          case (l, _ ~ r)    => ENe(l, r)
        }
    }
    lazy val e6: P[Expr] = e7 ~ rep(("<=" | "<" | ">=" | ">") ~ e7) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "<" ~ r)  => ELt(l, r)
          case (l, "<=" ~ r) => ELe(l, r)
          case (l, ">" ~ r)  => EGt(l, r)
          case (l, _ ~ r)    => EGe(l, r)
        }
    }
    lazy val e7: P[Expr] = e8 ~ rep(("++" | "+" | "-") ~ e8) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "+" ~ r) => EAdd(l, r)
          case (l, "-" ~ r) => ESub(l, r)
          case (l, _ ~ r)   => EConcat(l, r)
        }
    }
    lazy val e8: P[Expr] = e9 ~ rep(("*" | "/" | "%") ~ e9) ^^ {
      case e ~ es =>
        es.foldLeft(e) {
          case (l, "*" ~ r) => EMul(l, r)
          case (l, "/" ~ r) => EDiv(l, r)
          case (l, _ ~ r)   => EMod(l, r)
        }
    }
    lazy val e9: P[Expr] = "-" ~> e9 ^^ ENeg | "!" ~> e9 ^^ ENot | e10
    lazy val e10: P[Expr] = e11 ~ rep(
      opt("[" ~> repsep(ty, ",") <~ "]") ~
      ("(" ~> repsep(e0, ",") <~ ")"),
    ) ^^ {
      case f ~ as =>
        as.foldLeft(f) {
          case (f, tsOpt ~ as) => EApp(f, tsOpt.getOrElse(Nil), as)
        }
    }
    lazy val e11: P[Expr] = {
      "(" ~ ")" ^^^ EUnit |
      "(" ~> e0 <~ ")" |
      "{" ~> e0 <~ "}" |
      "exit" ~ "(" ~> e0 <~ ")" ^^ EExit.apply |
      num ^^ ENum.apply |
      bool ^^ EBool.apply |
      str ^^ EStr.apply |
      id ^^ EId.apply
    }
    // recursive definitions
    lazy val recDef: P[RecDef] =
      "lazy" ~ "val" ~> id ~ (":" ~> ty) ~ ("=" ~> e1) ^^ {
        case x ~ t ~ b => LazyVal(x, t, b)
      } |
      "def" ~> id ~ tvars ~ params ~ (":" ~> ty) ~ ("=" ~> e1) ^^ {
        case x ~ ts ~ ps ~ t ~ b => RecFun(x, ts, ps, t, b)
      } |
      "enum" ~> id ~ tvars ~ ("{" ~> rep1sep(variant, opt(";")) <~ "}") ^^ {
        case x ~ ts ~ vs => TypeDef(x, ts, vs)
      }
    // variants
    lazy val variant: P[Variant] =
      "case" ~> id ~ params ^^ { case x ~ ps => Variant(x, ps) }
    // match cases
    lazy val mcase: P[MatchCase] =
      "case" ~> id ~ ("(" ~> repsep(id, ",") <~ ")") ~ ("=>" ~> e0) ^^ {
        case x ~ ps ~ b => MatchCase(x, dupCheck(ps, "parameter"), b)
      }
    e0

  // parameters
  private lazy val params: P[List[Param]] =
    "(" ~> repsep(param, ",") <~ ")" ^^ { case ps => dupCheck(ps, "parameter") }
  private lazy val param: P[Param] =
    id ~ (":" ~> ty) ^^ { case x ~ t => Param(x, t) }

  // type variables
  private lazy val tvars: P[List[String]] =
    opt("[" ~> rep1sep(id, ",") <~ "]") ^^ {
      case xs => dupCheck(xs.getOrElse(Nil), "type variable")
    }

  // types
  private lazy val ty: P[Type] =
    lazy val t0: P[Type] =
      tvars ~ ("(" ~> repsep(t0, ",") <~ ")") ~ ("=>" ~> t0) ^^ {
        case tns ~ ps ~ b => ArrowT(tns, ps, b)
      } |
      tvars ~ t1 ~ ("=>" ~> t0) ^^ {
        case tns ~ p ~ b => ArrowT(tns, List(p), b)
      } |
      t1
    lazy val t1: P[Type] = {
      "(" ~> t0 <~ ")" |
      "Nothing" ^^^ NothingT |
      "Any" ^^^ AnyT |
      "Unit" ^^^ UnitT |
      "Number" ^^^ NumT |
      "Boolean" ^^^ BoolT |
      "String" ^^^ StrT |
      id ~ opt("[" ~> repsep(t0, ",") <~ "]") ^^ {
        case x ~ tsOpt => IdT(x, tsOpt.getOrElse(Nil))
      }
    }
    t0

  // desugaring rules
  val T: Expr = EBool(true)
  val F: Expr = EBool(false)
  def ENeg(expr: Expr): Expr = EMul(expr, ENum(-1))
  def ENot(expr: Expr): Expr = EIf(expr, F, T)
  def ESub(left: Expr, right: Expr): Expr = EAdd(left, ENeg(right))
  def EAnd(left: Expr, right: Expr): Expr = EIf(left, ENot(ENot(right)), F)
  def EOr(left: Expr, right: Expr): Expr = EIf(left, ENot(ENot(T)), right)
  def ENe(left: Expr, right: Expr): Expr = ENot(EEq(left, right))
  def ELe(left: Expr, right: Expr): Expr =
    EOr(ELt(left, right), EEq(left, right))
  def EGt(left: Expr, right: Expr): Expr = ENot(ELe(left, right))
  def EGe(left: Expr, right: Expr): Expr = ENot(ELt(left, right))

  // duplicate check
  private def dupCheck[T](
    names: List[T],
    kind: String,
    f: T => String = (x: T) => x.toString,
  ): List[T] =
    if (names.distinct.length != names.length)
      error(s"duplicate $kind: ${names.mkString(", ")}")
    names
}
