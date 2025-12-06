package kuplrg

import Implementation.*

class Spec extends SpecBase {

  // -------------------------------------------------------------------------
  // eval
  // -------------------------------------------------------------------------
  test(eval("()"), "(): Unit")
  test(eval("5"), "5: Number")
  test(eval("42"), "42: Number")
  test(eval("true"), "true: Boolean")
  test(eval("false"), "false: Boolean")
  test(eval("\"\""), "\"\": String")
  test(eval("\"hello\""), "\"hello\": String")
  // free identifier: x
  testExc(eval("x"))
  test(eval("1 + 2"), "3: Number")
  test(eval("3 + (2 + 3)"), "8: Number")
  test(eval("2 * 3"), "6: Number")
  test(eval("2 * (3 + 5)"), "16: Number")
  test(eval("5 / 2"), "2: Number")
  test(eval("532 / 3 / 20"), "8: Number")
  test(eval("\"\" ++ \"\""), "\"\": String")
  test(eval("\"\" ++ \"def\""), "\"def\": String")
  test(eval("\"abc\" ++ \"def\""), "\"abcdef\": String")
  // type mismatch: Boolean </: Number
  testExc(eval("1 + true"))
  // type mismatch: Number </: String
  testExc(eval("1 ++ 2"))
  test(eval("exit(\"\")"), "ERROR: Nothing")
  test(eval("exit(42) + 1"), "ERROR: Number")
  // type mismatch: Boolean </: Number
  testExc(eval("exit(1 + true)"))
  test(eval("exit(false) ++ exit(42)"), "ERROR: String")
  test(eval("if (true) exit(42) else true"), "ERROR: Boolean")
  test(eval("if (true) false else exit(true)"), "false: Boolean")
  test(eval("((x: String) => x)(exit(\"\"))"), "ERROR: String")
  test(eval("((x: Number=>Number) => x)(exit(0))"), "ERROR: Number => Number")
  test(eval("5 / 0"), "ERROR: Number")
  test(eval("5 / 0 + 3"), "ERROR: Number")
  test(eval("5 % 3"), "2: Number")
  test(eval("26362 % 52"), "50: Number")
  test(eval("5 % 0 * 10"), "ERROR: Number")
  test(eval("1 + 2 * 5 / 3 % 2"), "2: Number")
  test(eval("42 == 42"), "true: Boolean")
  test(eval("1 == 2"), "false: Boolean")
  test(eval("1 != 2"), "true: Boolean")
  test(eval("false == false"), "true: Boolean")
  test(eval("42 != false"), "true: Boolean")
  test(eval("42 == ((y: String) => y)"), "false: Boolean")
  test(eval("enum A { case X() }; X() == X()"), "true: Boolean")
  test(eval("enum A { case X(x: Number) }; X(1) == X(1)"), "true: Boolean")
  test(eval("enum A { case X(x: Number) }; X(2) == X(3)"), "false: Boolean")
  test(eval("((x: String) => x) == ((y: Number) => y)"), "false: Boolean")
  // type mismatch: B </: A
  testExc(eval("enum A {case X()}; val f=(a:A)=>42; enum B {case X()}; f(X())"))
  test(eval("1 < 2"), "true: Boolean")
  test(eval("3 < 2"), "false: Boolean")
  test(eval("1 <= 2"), "true: Boolean")
  test(eval("2 <= 2"), "true: Boolean")
  test(eval("9 <= 2"), "false: Boolean")
  test(eval("5 > 2"), "true: Boolean")
  test(eval("-42 > 2"), "false: Boolean")
  test(eval("1 >= 2"), "false: Boolean")
  test(eval("2 >= 2"), "true: Boolean")
  test(eval("3 >= 2"), "true: Boolean")
  test(eval("1; true; 2"), "2: Number")
  test(eval("1 / 0; true"), "ERROR: Boolean")
  test(eval("false && true"), "false: Boolean")
  test(eval("false && (1 / 0 > 2)"), "false: Boolean")
  test(eval("false || true"), "true: Boolean")
  test(eval("true || (1 / 0 > 2)"), "true: Boolean")
  // type mismatch: Number </: Boolean
  testExc(eval("true && 1"))
  // type mismatch: Number </: Boolean
  testExc(eval("false && 1"))
  // type mismatch: Number </: Boolean
  testExc(eval("1 && true"))
  // type mismatch: Number </: Boolean
  testExc(eval("1 || true"))
  test(eval("if (true) () else ()"), "(): Unit")
  test(eval("if (true) 1 else 2"), "1: Number")
  test(
    eval("if (true) { def f[T](x: T):T = x; f } else def g[U](y: U): U = y; g"),
    "<function>: [T](T => T)",
  )
  test(eval("if (true) 1 else false"), "1: Any")
  test(
    eval("if (true) (x: Number) => x else (y: Any) => y"),
    "<function>: Number => Any",
  )
  test(eval("val x = 42; x"), "42: Number")
  test(eval("val x: Number = 42; x"), "42: Number")
  // type mismatch: Number </: Boolean
  testExc(eval("val x: Boolean = 42; x"))
  // unknown type: T
  testExc(eval("val x: T = 42; x"))
  test(eval("val x = 1; val y = 2; x + y"), "3: Number")
  test(eval("() => 42"), "<function>: () => Number")
  test(eval("(x: Number) => x"), "<function>: Number => Number")
  test(eval("(x: Boolean) => x"), "<function>: Boolean => Boolean")
  test(
    eval(
      "(x: Number, y: Number) => x + y",
    ),
    "<function>: (Number, Number) => Number",
  )
  test(eval("val f = (x: Number) => x; f"), "<function>: Number => Number")
  // unknown type: T
  testExc(eval("(x: T) => x"))
  // not a function: Number
  testExc(eval("1(2)"))
  // not a function: Number
  testExc(eval("(x: Number) => x(1)"))
  // type mismatch: Number </: Number => Number
  testExc(eval("(x: (Number => Number) => Number) => x(1)"))
  test(eval("val f = (n: Number) => (m: Number) => m+n; f(3)(4)"), "7: Number")
  test(
    eval("val f = (x: Unit, y: String, z: Boolean) => x; f"),
    "<function>: (Unit, String, Boolean) => Unit",
  )
  test(
    eval("val f = (x: Unit, y: String, z: Boolean) => y; f"),
    "<function>: (Unit, String, Boolean) => String",
  )
  test(
    eval("val f = (x: Unit, y: String, z: Boolean) => z; f"),
    "<function>: (Unit, String, Boolean) => Boolean",
  )
  test(eval("val f = (x: Number) => x; f(42)"), "42: Number")
  test(eval("val f = (x: Number) => (y: Number) => x*y; f(5)(7)"), "35: Number")
  test(
    eval(
      "(f: Number => Boolean) => (x: Number) => f(x)",
    ),
    "<function>: (Number => Boolean) => Number => Boolean",
  )
  test(
    eval(
      "(f: Number => Boolean, x: Number) => f(x)",
    ),
    "<function>: (Number => Boolean, Number) => Boolean",
  )
  test(
    eval(
      "(x: Number) => (y: Number) => x * y",
    ),
    "<function>: Number => Number => Number",
  )
  test(eval("lazy val x: Number = 42; x"), "42: Number")
  test(eval("lazy val x: Number = 1 / 0; true"), "true: Boolean")
  test(eval("lazy val x: Number = y+1; lazy val y: Number = 1; x"), "2: Number")
  test(eval("lazy val x: Number = x; 42"), "42: Number")
  test(eval("lazy val x: Number = 1 + x; 42"), "42: Number")
  test(eval("lazy val x: Number = x * x; 42"), "42: Number")
  test(
    eval("lazy val x: Number = y + 1; lazy val y: Number = x + 1; true"),
    "true: Boolean",
  )
  test(
    eval("lazy val x: Boolean = if (x) x else x; \"abc\""),
    "\"abc\": String",
  )
  test(eval("lazy val x: Any = 42; x"), "42: Any")
  test(eval("lazy val x: Number => Any = (y: Any) => 42; x(1)"), "42: Any")
  // type mismatch: Number => Number </: Any => Number
  testExc(eval("lazy val x: Any => Number = (y: Number) => y; x"))
  // type mismatch: Boolean </: Number
  testExc(eval("lazy val x: Number = true; x"))
  // type mismatch: Number </: Boolean
  testExc(eval("lazy val x: Boolean = if (x) 1 else 2; x"))
  // unknown type: T
  testExc(eval("lazy val x: T = 42; x"))
  test(
    eval(
      "def f(x: Number): Number = x + 1; f",
    ),
    "<function>: Number => Number",
  )
  test(
    eval(
      "def f(x: Number): Number = x + 1; f(10)",
    ),
    "11: Number",
  )
  test(
    eval(
      "def sum(n: Number): Number = if (n > 0) n + sum(n - 1) else 0; sum",
    ),
    "<function>: Number => Number",
  )
  test(
    eval(
      "def sum(n: Number): Number = if (n > 0) n + sum(n - 1) else 0; sum(10)",
    ),
    "55: Number",
  )
  test(
    eval(
      "def fib(k: Number): Number = if (k < 2) 1 else fib(k-1) + fib(k-2); fib",
    ),
    "<function>: Number => Number",
  )
  test(
    eval(
      "def fib(k: Number): Number = if (k < 2) 1 else fib(k-1) + fib(k-2); fib(7)",
    ),
    "21: Number",
  )
  test(
    eval(
      "def twice(f: Number => Number, n: Number): Number = f(f(n));" +
      "twice((x: Number) => x + 1, 0)",
    ),
    "2: Number",
  )
  test(
    eval(
      "def myIf(c: Boolean, t: Number, e: Number): Number = if (c) t else e;" +
      "myIf(true, 1, 2)",
    ),
    "1: Number",
  )
  // type mismatch: Boolean </: Number
  testExc(eval("def f(x: Number): Number = true; f"))
  // unknown type: T
  testExc(eval("def f(x: T): T = x; f"))
  test(eval("def f[T](x: T): T = x; f"), "<function>: [T](T => T)")
  test(
    eval(
      "def f[T, U](x: T, y: U): T = x; f",
    ),
    "<function>: [T, U]((T, U) => T)",
  )
  test(
    eval(
      "def f[T, U](g: T => U, x: T): U = g(x)" +
      "f",
    ),
    "<function>: [T, U]((T => U, T) => U)",
  )
  test(
    eval(
      "def f[T, U](g: T => U, x: T): U = g(x)" +
      "f[Number, Number => Number]((x: Number) => (y: Number) => x + y, 1)",
    ),
    "<function>: Number => Number",
  )
  // unknown type: U
  testExc(eval("def f[T](x: T): T = x; f[U](42)"))
  // already defined type: T
  testExc(eval("def f[T](x: T): T = { enum T { case X() }; x }; f"))
  // already defined type: T
  testExc(eval("enum T { case X() }; def f[T](x: T): T = x; f"))
  // already defined type: T
  testExc(eval("def f[T](x: T): T = def g[T](z: T): T = z; g(x); f"))
  val shape = "enum Shape { " +
    "case Square(side: Number)" +
    "case Rect(width: Number, height: Number) }"
  // unknown type: Shape
  testExc(eval(shape + "Square"))
  // unknown type: Shape
  testExc(eval(shape + "Square(42)"))
  // free identifier: Circle
  testExc(eval(shape + "Circle"))
  // type mismatch: Boolean </: Number
  testExc(eval(shape + "Square(true)"))
  // arity mismatch: 1 != 2
  testExc(eval(shape + "Square(10, 10)"))
  // arity mismatch: 2 != 1
  testExc(eval(shape + "Rect(3)"))
  test(
    eval(
      shape +
      "Square(10) match { case Square(n) => n * n; case Rect(w, h) => w * h }",
    ),
    "100: Number",
  )
  test(
    eval(
      shape +
      "Rect(3, 5) match { case Square(n) => n * n; case Rect(w, h) => w * h }",
    ),
    "15: Number",
  )
  // unknown variant: Circle
  testExc(eval(shape + "Rect(3, 5) match { case Circle(n) => n * n }"))
  // missing case: Square
  testExc(eval(shape + "Rect(3, 5) match { case Rect(n, m) => n * m }"))
  // duplicate case: Square
  testExc(
    eval(
      shape + "Square(3) match { case Square(n) => n * n; case Square (n) => n }",
    ),
  )
  // ---------------------------------------------------------------------------
  // Natural numbers
  // ---------------------------------------------------------------------------
  val natHelper = """
    enum Nat {
      case Zero()
      case Succ(n: Nat)
    }
    def nat2num(n: Nat): Number = n match {
      case Zero() => 0
      case Succ(n) => 1 + nat2num(n)
    }
    def num2nat(n: Number): Nat = {
      if (n <= 0) Zero()
      else Succ(num2nat(n - 1))
    }
    def add(n: Nat, m: Nat): Nat = n match {
      case Zero() => m
      case Succ(n) => Succ(add(n, m))
    }
    def mul(n: Nat, m: Nat): Nat = n match {
      case Zero() => Zero()
      case Succ(n) => add(m, mul(n, m))
    }
    def pow(n: Nat, m: Nat): Nat = m match {
      case Zero() => Succ(Zero())
      case Succ(m) => mul(n, pow(n, m))
    }
  """
  test(eval(natHelper + "nat2num(Succ(Succ(Succ(Zero()))))"), "3: Number")
  test(eval(natHelper + "nat2num(add(num2nat(2), num2nat(3)))"), "5: Number")
  test(eval(natHelper + "nat2num(mul(num2nat(2), num2nat(3)))"), "6: Number")
  test(eval(natHelper + "nat2num(pow(num2nat(2), num2nat(3)))"), "8: Number")
  // ---------------------------------------------------------------------------
  // Lists
  // ---------------------------------------------------------------------------
  val listHelper = """
    enum List[T] {
      case Nil()
      case Cons(head: T, tail: List[T])
    }
    def length[T](l: List[T]): Number = l match {
      case Nil() => 0
      case Cons(x, xs) => 1 + length[T](xs)
    }
    def sum(l: List[Number]): Number = l match {
      case Nil() => 0
      case Cons(x, xs) => x + sum(xs)
    }
    def map[T, U](l: List[T], f: T => U): List[U] = l match {
      case Nil() => Nil[U]()
      case Cons(x, xs) => Cons[U](f(x), map[T, U](xs, f))
    }
    def filter[T](l: List[T], f: T => Boolean): List[T] = l match {
      case Nil() => Nil[T]()
      case Cons(x, xs) => if (f(x)) Cons[T](x, filter[T](xs, f)) else filter[T](xs, f)
    }
    def contains[T](l: List[T], x: T): Boolean = l match {
      case Nil() => false
      case Cons(y, ys) => if (x == y) true else contains[T](ys, x)
    }
    def append[T](l1: List[T], l2: List[T]): List[T] = l1 match {
      case Nil() => l2
      case Cons(x, xs) => Cons[T](x, append[T](xs, l2))
    }
    def foldLeft[T, U](l: List[T], z: U, f: (U, T) => U): U = l match {
      case Nil() => z
      case Cons(x, xs) => foldLeft[T, U](xs, f(z, x), f)
    }
    def mkString[T](l: List[T], f: T => String, sep: String): String = l match {
      case Nil() => ""
      case Cons(x, xs) =>
        foldLeft[T, String](xs, f(x), (s: String, x: T) => s ++ sep ++ f(x))
    }
  """
  val list1 = "Cons[Number](1, Cons[Number](2, Cons[Number](3, Nil[Number]())))"
  val list2 = "Cons[Number](4, Cons[Number](5, Nil[Number]()))"
  val list3 =
    "Cons[String](\"a\", Cons[String](\"b\", Cons[String](\"c\", Nil[String]())))"
  test(
    eval(listHelper + "sum(Nil[Number]())"),
    "0: Number",
  )
  test(
    eval(listHelper + "length[Any](" + list1 + ")"),
    "3: Number",
  )
  test(
    eval(listHelper + "length[Any](append[Any](" + list1 + ", " + list3 + "))"),
    "6: Number",
  )
  test(
    eval(listHelper + "sum(" + list1 + ")"),
    "6: Number",
  )
  test(
    eval(
      listHelper + "sum(map[Number, Number](" + list1 + ", (x: Number) => x * x))",
    ),
    "14: Number",
  )
  test(
    eval(
      listHelper + "sum(filter[Number](" + list1 + ", (x: Number) => x % 2 == 1))",
    ),
    "4: Number",
  )
  test(
    eval(
      listHelper + "contains[Number](" + list1 + ", 2)",
    ),
    "true: Boolean",
  )
  test(
    eval(
      listHelper + "contains[Number](" + list1 + ", 6)",
    ),
    "false: Boolean",
  )
  test(
    eval(
      listHelper + "sum(append[Number](" + list1 + ", " + list2 + "))",
    ),
    "15: Number",
  )
  test(
    eval(
      listHelper + "foldLeft[Number, Number](Nil[Number](), 0, (x: Number, y: Number) => x + y)",
    ),
    "0: Number",
  )
  test(
    eval(
      listHelper + "foldLeft[Number, Number](" + list1 + ", 0, (x: Number, y: Number) => x + y)",
    ),
    "6: Number",
  )
  test(
    eval(
      listHelper + "mkString[String](" + list3 + ", (x: String) => x, \", \")",
    ),
    "\"a, b, c\": String",
  )
  test(
    eval(
      listHelper + "mkString[String](" + list3 + ", (x: String) => \"|\" ++ x ++ \"|\", \" ~ \")",
    ),
    "\"|a| ~ |b| ~ |c|\": String",
  )
  test(
    eval(
      listHelper + "mkString[Boolean](map[Number, Boolean](" + list1 + ", (x: Number) => x % 2 == 0), (b: Boolean) => if (b) \"TRUE\" else \"FALSE\", \" | \")",
    ),
    "\"FALSE | TRUE | FALSE\": String",
  )
  // ---------------------------------------------------------------------------
  // Trees
  // ---------------------------------------------------------------------------
  val treeHelper = s"""
    $listHelper
    enum Tree[T] {
      case Leaf(value: T)
      case Node(left: Tree[T], value: T, right: Tree[T])
    }
    def sumTree(t: Tree[Number]): Number = t match {
      case Leaf(x) => x
      case Node(l, x, r) => sumTree(l) + x + sumTree(r)
    }
    def mapTree[T](t: Tree[T], f: T => T): Tree[T] = t match {
      case Leaf(x) => Leaf[T](f(x))
      case Node(l, x, r) => Node[T](mapTree[T](l, f), f(x), mapTree[T](r, f))
    }
    def flatten[T](t: Tree[T]): List[T] = t match {
      case Leaf(x) => Cons[T](x, Nil[T]())
      case Node(l, x, r) => append[T](flatten[T](l), Cons[T](x, flatten[T](r)))
    }
    val tree = Node[Number](Leaf[Number](1), 2, Node[Number](Leaf[Number](3), 4, Leaf[Number](5)))
  """
  test(
    eval(
      treeHelper + "sumTree(Leaf[Number](42))",
    ),
    "42: Number",
  )
  test(
    eval(
      treeHelper + "sumTree(tree)",
    ),
    "15: Number",
  )
  test(
    eval(
      treeHelper + "sumTree(mapTree[Number](tree, (x: Number) => x * x))",
    ),
    "55: Number",
  )
  test(
    eval(
      treeHelper + "sumTree(mapTree[Number](tree, (x: Number) => x / 2))",
    ),
    "6: Number",
  )
  test(
    eval(
      treeHelper + "sum(flatten[Number](tree))",
    ),
    "15: Number",
  )
  test(
    eval(
      treeHelper + "contains[Number](flatten[Number](tree), 2)",
    ),
    "true: Boolean",
  )
  test(
    eval(
      treeHelper + "contains[Number](flatten[Number](tree), 7)",
    ),
    "false: Boolean",
  )
  test(
    eval(
      treeHelper + "sum(append[Number](flatten[Number](tree), Cons[Number](6, Nil[Number]())))",
    ),
    "21: Number",
  )
  // ---------------------------------------------------------------------------
  // Maps
  // ---------------------------------------------------------------------------
  val mapHelper = """
    enum Map[V] {
      case Empty()
      case Put(m: Map[V], k: String, v: V)
    }
    def get[V](m: Map[V], k: String): V = m match {
      case Empty() => exit("not found: " ++ k)
      case Put(m, k1, v) => if (k == k1) v else get[V](m, k)
    }
  """
  // unknown type: Map
  testExc(eval(mapHelper + "Empty[Number]()"))
  // unknown type: Map
  testExc(eval(mapHelper + "() => Empty[Any]()"))
  test(
    eval(
      mapHelper + "get[Number](Put[Number](Empty[Number](), \"a\", 42), \"a\")",
    ),
    "42: Number",
  )
  test(
    eval(
      mapHelper + "get[Boolean](Put[Boolean](Empty[Boolean](), \"a\", true), \"b\")",
    ),
    "ERROR: Boolean",
  )
  val expr1 = """
    def gcd(a: Number): Number => Number = (b: Number) => {
      if (a == 0) b else gcd(b % a)(a)
    }
    gcd(432)(180)
  """
  test(eval(expr1), "36: Number")
  val expr2 = """
    def fact(n: Number): Number = if (n > 0) n * fact(n - 1) else 1
    fact(10)
  """
  test(eval(expr2), "3628800: Number")
  val expr3 = """
    def isPrime(n: Number): Boolean =
      def iter(k: Number): Boolean =
        if (k * k > n) true
        else if (n % k == 0) false
        else iter(k + 1)
      if (n < 2) false
      else iter(2)
    isPrime(1000003)
  """
  test(eval(expr3), "true: Boolean")
  val expr4 = """
    def sum(n: Number): Number =
      def iter(k: Number): Number => Number = (acc: Number) =>
        if (k > n) acc
        else iter(k + 1)(acc + k)
      iter(1)(0)
    sum(100)
  """
  test(eval(expr4), "5050: Number")
  val expr5 = """
    def findKth(f: Number => Boolean): Number => Number = (k: Number) =>
      def iter(n: Number): Number => Number = (k: Number) =>
        if (f(n)) {
          if (k == 1) n else iter(n + 1)(k - 1)
        } else {
          iter(n + 1)(k)
        }
      iter(0)(k)
    findKth((x: Number) => x % 3 == 2)(43)
  """
  test(eval(expr5), "128: Number")
  val expr6 = """
    def isPrime(n: Number): Boolean =
      def iter(k: Number): Boolean =
        if (k * k > n) true
        else if (n % k == 0) false
        else iter(k + 1)
      if (n < 2) false
      else iter(2)
    def findKth(f: Number => Boolean): Number => Number = (k: Number) =>
      def iter(n: Number): Number => Number = (k: Number) =>
        if (f(n)) {
          if (k == 1) n else iter(n + 1)(k - 1)
        } else {
          iter(n + 1)(k)
        }
      iter(0)(k)
    findKth(isPrime)(101)
  """
  test(eval(expr6), "547: Number")
  val expr7 = """
    val addN = (n: Number) => (x: Number) => x + n
    def isEven(x: Number): Boolean = x % 2 == 0
    def findKth(f: Number => Boolean): Number => Number = (k: Number) =>
      def iter(n: Number): Number => Number = (k: Number) =>
        if (f(n)) {
          if (k == 1) n else iter(n + 1)(k - 1)
        } else {
          iter(n + 1)(k)
        }
      iter(0)(k)
    findKth((n: Number) => isEven(addN(n)(1)))(23)
  """
  test(eval(expr7), "45: Number")
  val expr8 = """
    val sum = (n: Number) => {
      (map: Number => Number) => {
        (filter: Number => Boolean) => {
          def iter(k: Number): Number => Number = (acc: Number) =>
            if (k > n) acc
            else iter(k + 1)(acc + (if (filter(k)) map(k) else 0))
          iter(1)(0)
        }
      }
    }
    val square = (x: Number) => x * x
    val isOdd = (x: Number) => x % 2 == 1
    sum(10)(square)(isOdd)
  """
  test(eval(expr8), "165: Number")
  val expr9 = """
    val fold = {
      (f: Number => Number => Number) =>
      (default: Number) =>
      (from: Number) =>
      (to: Number) =>
        def iter(k: Number): Number => Number = (acc: Number) =>
          if (k > to) acc
          else iter(k + 1)(f(acc)(k))
        iter(from)(default)
    }
    val add = (x: Number) => (y: Number) => x + y
    fold(add)(0)(53)(78)
  """
  test(eval(expr9), "1703: Number")
  val expr10 = """
    enum T { case T(f: T => Number => Number) }
    val mkRec = (body: (Number => Number) => Number => Number) => {
      val fX = (fY: T) => {
        val f = (x: Number) => fY match { case T(fZ) => fZ(fY)(x) };
        body(f)
    };
    fX(T(fX)) };
    val sum = mkRec((sum: Number => Number) => (n: Number) =>
      if (n < 1) 0
      else n + sum(n + -1));
    sum(10)
  """
  test(eval(expr10), "55: Number")
  val expr11 = """
    enum A {
      case X(x: Number)
    }
    def get(a: A): Number = a match {
      case X(n) => n
    }
    {
      enum A {
        case X(x: Boolean)
      }
      get(X(true))
    }
  """
  // already defined type: A
  testExc(eval(expr11))
  val expr12 = """
    val get = {
      enum A {
        case X(x: Number)
      }
      (a: A) => a match {
        case X(n) => n
      }
    }
    enum A {
      case X(x: Boolean)
    }
    get(X(true))
  """
  // unknown type: A
  testExc(eval(expr12), "")
  val expr13 = """{
    val f = {
      enum A { case X(x: Number) }
      (n: Number) => X(n)
    }
    f(42)
  }"""
  // unknown type: A
  testExc(eval(expr13))
  val expr14 = """{
    val f = {
      enum A { case X(x: Number) }
      (n: Number) => X(n)
    }
    f(42) match {
      case X(n) => n
    }
  }"""
  // unknown type: A
  testExc(eval(expr14))
  val expr15 = s"""{
    $listHelper
    enum Expr {
      case Num(number: Number)
      case Add(left: Expr, right: Expr)
      case Mul(left: Expr, right: Expr)
    }
    def interp(expr: Expr): Number = expr match {
      case Num(n)    => n
      case Add(l, r) => interp(l) + interp(r)
      case Mul(l, r) => interp(l) * interp(r)
    }
    interp(
      Mul(
        Add(Num(1), Num(2)),
        Add(Num(3), Num(4))
      )
    )
  }"""
  test(eval(expr15), "21: Number")
  val expr16 = s"""
    $listHelper
    $mapHelper
    enum Expr {
      case Num(number: Number)
      case Add(left: Expr, right: Expr)
      case Mul(left: Expr, right: Expr)
      case Val(name: String, init: Expr, body: Expr)
      case Id(name: String)
      case Fun(param: String, ty: Type, body: Expr)
      case App(fun: Expr, arg: Expr)
      case TypeAbs(name: String, body: Expr)
      case TypeApp(expr: Expr, ty: Type)
    }
    enum Type {
      case NumT()
      case ArrowT(paramTy: Type, retTy: Type)
      case VarT(name: String)
      case PolyT(name: String, ty: Type)
    }
    enum TypeEnv { case TypeEnv(vars: Map[Type], tys: List[String]) }
    enum Env { case Env(vars: Map[Value]) }
    enum Value {
      case NumV(number: Number)
      case CloV(param: String, body: Expr, env: Env)
      case TypeAbsV(name: String, body: Expr, env: Env)
    }
    def addVar(env: Env, name: String, v: Value): Env = env match {
      case Env(vars) => Env(Put[Value](vars, name, v))
    }
    def typeStr(ty: Type): String = ty match {
      case NumT()             => "Number"
      case ArrowT(p, b)       => "(" ++ typeStr(p) ++ " => " ++ typeStr(b) ++ ")"
      case VarT(x)            => x
      case PolyT(x, t)        => "[" ++ x ++ "](" ++ typeStr(t) ++ ")"
    }
    def str(value: Value): String = value match {
      case NumV(n) =>
        if (n == 0) "0"
        else if (n == 1) "1"
        else if (n == 2) "2"
        else "<number>"
      case CloV(param, body, env) => "<function>"
      case TypeAbsV(name, body, env) => "<type-abs>"
    }
    def isSame(lty: Type, rty: Type): Boolean = lty match {
      case NumT() => rty match {
        case NumT() => true
        case ArrowT(p, r) => false
        case VarT(x) => false
        case PolyT(x, t) => false
      }
      case ArrowT(lparamTy, lretTy) => rty match {
        case NumT() => false
        case ArrowT(rparamTy, rretTy) =>
          isSame(lparamTy, rparamTy) && isSame(lretTy, rretTy)
        case VarT(x) => false
        case PolyT(x, t) => false
      }
      case VarT(lname) => rty match {
        case NumT() => false
        case ArrowT(p, r) => false
        case VarT(rname) => lname == rname
        case PolyT(x, t) => false
      }
      case PolyT(lname, lty) => rty match {
        case NumT() => false
        case ArrowT(p, r) => false
        case VarT(x) => false
        case PolyT(rname, rty) => lname == rname && isSame(lty, rty)
      }
    }
    def mustSame(lty: Type, rty: Type): Unit = {
      if (!isSame(lty, rty)) exit(typeStr(lty) ++ " != " ++ typeStr(rty))
      else ()
    }
    def numBOpTy(left: Type, right: Type): Type = {
      mustSame(left, NumT())
      mustSame(right, NumT())
      NumT()
    }
    def mustValid(ty: Type, tenv: TypeEnv): Type = ty match {
      case NumT() => NumT()
      case ArrowT(pty, rty) =>
        ArrowT(mustValid(pty, tenv), mustValid(rty, tenv))
      case VarT(name) =>
        val tys = tenv match { case TypeEnv(_, tys) => tys }
        if (!contains[String](tys, name)) exit("unknown type: " ++ name)
        else ()
        VarT(name)
      case PolyT(name, ty) => PolyT(name, mustValid(ty, tenv match {
        case TypeEnv(vars, tys) => TypeEnv(vars, Cons[String](name, tys))
      }))
    }
    def subst(bodyTy: Type, name: String, ty: Type): Type = bodyTy match {
      case NumT() => NumT()
      case ArrowT(pty, rty) =>
        ArrowT(subst(pty, name, ty), subst(rty, name, ty))
      case VarT(x) =>
        if (name == x) ty else VarT(x)
      case PolyT(x, bodyTy) =>
        if (name == x) PolyT(x, bodyTy)
        else PolyT(x, subst(bodyTy, name, ty))
    }
    def typeCheck(expr: Expr, tenv: TypeEnv): Type = expr match {
      case Num(_) => NumT()
      case Add(left, right) =>
        numBOpTy(typeCheck(left, tenv), typeCheck(right, tenv))
      case Mul(left, right) =>
        numBOpTy(typeCheck(left, tenv), typeCheck(right, tenv))
      case Val(name, init, body) =>
        val initTy = typeCheck(init, tenv)
        typeCheck(body, tenv match {
          case TypeEnv(vars, tys) => TypeEnv(Put[Type](vars, name, initTy), tys)
        })
      case Id(name) => get[Type](tenv match { case TypeEnv(vs, _) => vs }, name)
      case Fun(param, ty, body) =>
        mustValid(ty, tenv)
        ArrowT(ty, typeCheck(body, tenv match {
          case TypeEnv(vars, tys) => TypeEnv(Put[Type](vars, param, ty), tys)
        }))
      case App(fun, arg) => typeCheck(fun, tenv) match {
        case ArrowT(paramTy, retTy) =>
          mustSame(paramTy, typeCheck(arg, tenv))
          retTy
        case NumT() => exit("not a function")
        case VarT(x) => exit("not a function")
        case PolyT(x, t) => exit("not a function")
      }
      case TypeAbs(name, body) =>
        val tys = tenv match { case TypeEnv(_, tys) => tys }
        if (contains[String](tys, name)) exit("already defined: " ++ name)
        else ()
        PolyT(name, typeCheck(body, tenv match {
          case TypeEnv(vars, tys) => TypeEnv(vars, Cons[String](name, tys))
        }))
      case TypeApp(expr, ty) => typeCheck(expr, tenv) match {
        case PolyT(name, bodyTy) => subst(bodyTy, name, mustValid(ty, tenv))
        case NumT() =>
          exit("not a polymorphic type: " ++ typeStr(NumT()))
        case ArrowT(p, r) =>
          exit("not a polymorphic type: " ++ typeStr(ArrowT(p, r)))
        case VarT(x) =>
          exit("not a polymorphic type: " ++ typeStr(VarT(x)))
      }
    }
    def getNum(value: Value): Number = value match {
      case NumV(n) => n
      case CloV(p, b, e) => exit("not a number")
      case TypeAbsV(n, b, e) => exit("not a number")
    }
    def interp(expr: Expr, env: Env): Value = expr match {
      case Num(n) => NumV(n)
      case Add(l, r) => NumV(getNum(interp(l, env)) + getNum(interp(r, env)))
      case Mul(l, r) => NumV(getNum(interp(l, env)) * getNum(interp(r, env)))
      case Val(x, i, b) => interp(b, addVar(env, x, interp(i, env)))
      case Id(x) => get[Value](env match { case Env(vars) => vars }, x)
      case Fun(p, _, b) => CloV(p, b, env)
      case App(f, e) => interp(f, env) match {
        case CloV(p, b, fenv) =>
          interp(b, addVar(fenv, p, interp(e, env)))
        case NumV(n) =>
          exit("not a function but a number")
        case TypeAbsV(n, b, e) =>
          exit("not a function but a type abstraction")
      }
      case TypeAbs(name, body) => TypeAbsV(name, body, env)
      case TypeApp(expr, ty) => interp(expr, env) match {
        case TypeAbsV(name, body, env) => interp(body, env)
        case NumV(n) => exit("not a type abstraction but a number")
        case CloV(p, b, e) => exit("not a type abstraction but a function")
      }
    }
    def eval(expr: Expr): String = {
      val ty = typeCheck(expr, TypeEnv(Empty[Type](), Nil[String]()))
      val v = interp(expr, Env(Empty[Value]()))
      str(v) ++ ": " ++ typeStr(ty)
    }
    val expr1 = Val(
      "f",
      TypeAbs("T", Fun("x", VarT("T"), Id("x"))),
      App(
        TypeApp(Id("f"),NumT()),
        Num(1)
      )
    )
    val expr2 = Val(
      "f",
      TypeAbs("T", Fun("x", VarT("T"), Id("x"))),
      App(
        TypeApp(Id("f"), ArrowT(NumT(), NumT())),
        Fun("x", NumT(), Add(Id("x"), Num(1)))
      )
    )
    val expr3 = Val(
      "f",
      TypeAbs("T", Fun("x", VarT("T"), Id("x"))),
      App(
        App(
          TypeApp(Id("f"), ArrowT(NumT(), NumT())),
          Fun("x", NumT(), Add(Id("x"), Num(1)))
        ),
        Num(1)
      )
    )
    "<expr1> ---> " ++ eval(expr1) ++ " | " ++
    "<expr2> ---> " ++ eval(expr2) ++ " | " ++
    "<expr3> ---> " ++ eval(expr3)
  """
  test(
    eval(expr16),
    "\"<expr1> ---> 1: Number | <expr2> ---> <function>: (Number => Number) | <expr3> ---> 2: Number\": String",
    weight = 20,
  )

  /* Write your own tests */

}
