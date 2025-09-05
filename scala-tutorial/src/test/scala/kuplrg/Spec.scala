package kuplrg

import Implementation.*

class Spec extends SpecBase {
  // tests for `clamp`
  test(clamp(2, 3, 5), 3)
  test(clamp(2, 1, 5), 2)
  test(clamp(2, 7, 5), 5)
  test(clamp(-1, 0, 3), 0)
  test(clamp(-3, -5, -1), -3)

  // tests for `validName`
  test(validName(""), false)
  test(validName("Alice"), true)
  test(validName("Overlylongname"), false)
  test(validName("With Space"), true)
  test(validName("lowercase"), false)

  // tests for `collatzLength`
  test(collatzLength(1), 1)
  test(collatzLength(2), 2)
  test(collatzLength(3), 8)
  test(collatzLength(4), 3)
  test(collatzLength(5), 6)

  // tests for `fixpoint`
  test(fixpoint(_ / 2)(20), 0)
  test(fixpoint(_.abs)(-15), 15)
  def gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a % b)
  test(fixpoint(gcd(48, _))(18), 6)
  def sumDigits(n: Int): Int = n.toString.map(_.asDigit).sum
  test(fixpoint(sumDigits)(123456), 3)
  def productDigits(n: Int): Int = n.toString.map(_.asDigit).product
  test(fixpoint(productDigits)(327), 8)

  // tests for `applyK`
  test(applyK(_ + 3, 2)(1), 7)
  test(applyK(_ + 2, 5)(7), 17)
  test(applyK(_ * 2, 10)(1), 1024)
  test(applyK(_ * 10, 3)(42), 42000)
  test(applyK(productDigits, 2)(327), 8)

  // tests for `sumEven`
  test(sumEven(Nil), 0)
  test(sumEven(List(1, 3, 5)), 0)
  test(sumEven(List(2, 4, 6)), 12)
  test(sumEven(List(1, 2, 3, 4, 5)), 6)
  test(sumEven(List(1, 2, 3, 4, 5, 6)), 12)

  // tests for `double`
  test(double(Nil), Nil)
  test(double(List(42)), List(42, 42))
  test(double(List(1, 2, 3)), List(1, 1, 2, 2, 3, 3))
  test(double(List(5, 5, 5)), List(5, 5, 5, 5, 5, 5))
  test(double(List(1, 2, 3, 4)), List(1, 1, 2, 2, 3, 3, 4, 4))

  // tests for `generate`
  test(generate(_ / 2)(20), List(20, 10, 5, 2, 1, 0))
  test(generate(_.abs)(-15), List(-15, 15))
  test(generate(gcd(48, _))(18), List(18, 6))
  test(generate(sumDigits)(123456), List(123456, 21, 3))
  test(generate(productDigits)(327), List(327, 42, 8))

  // tests for `join`
  val m1: Map[String, Int] = Map("A" -> 1, "B" -> 2, "C" -> 3)
  val m2: Map[String, Int] = Map("B" -> 3, "C" -> 4, "D" -> 5)
  val m3: Map[String, Int] = Map("A" -> 2, "C" -> 1)
  test(join(m1, Map()), m1)
  test(join(Map(), m1), m1)
  test(join(m1, m2), Map("A" -> 1, "B" -> 5, "C" -> 7, "D" -> 5))
  test(join(m1, m3), Map("A" -> 3, "B" -> 2, "C" -> 4))
  test(join(m2, m3), Map("A" -> 2, "B" -> 3, "C" -> 5, "D" -> 5))

  // tests for `subsets`
  test(subsets(Set()), Nil)
  test(subsets(Set(1)), List(Set(1)))
  test(subsets(Set(1, 2)), List(Set(1), Set(1, 2), Set(2)))
  test(
    subsets(Set(3, 2, 1)),
    List(
      Set(1),
      Set(1, 2),
      Set(1, 2, 3),
      Set(1, 3),
      Set(2),
      Set(2, 3),
      Set(3),
    ),
  )
  test(
    subsets(Set(1, 2, 3, 4)),
    List(
      Set(1),
      Set(1, 2),
      Set(1, 2, 3),
      Set(1, 2, 3, 4),
      Set(1, 2, 4),
      Set(1, 3),
      Set(1, 3, 4),
      Set(1, 4),
      Set(2),
      Set(2, 3),
      Set(2, 3, 4),
      Set(2, 4),
      Set(3),
      Set(3, 4),
      Set(4),
    ),
  )

  // ---------------------------------------------------------------------------
  // Trees
  // ---------------------------------------------------------------------------
  import Tree.*

  //  8
  val tree1: Tree = Leaf(8)

  //    1
  //   / \
  //  2   3
  val tree2: Tree = Branch(Leaf(2), 1, Leaf(3))

  //    4
  //   / \
  //  5   2
  //     / \
  //    8   3
  val tree3: Tree = Branch(Leaf(5), 4, Branch(Leaf(8), 2, Leaf(3)))

  //    7
  //   / \
  //  2   3
  //     / \
  //    5   1
  //   / \
  //  1   8
  val tree4: Tree =
    Branch(Leaf(2), 7, Branch(Branch(Leaf(1), 5, Leaf(8)), 3, Leaf(1)))

  //      42
  //     /  \
  //    7    7
  //   / \   / \
  //  7   9 3   4
  val tree5: Tree =
    Branch(Branch(Leaf(7), 7, Leaf(9)), 42, Branch(Leaf(3), 7, Leaf(4)))

  // tests for `heightOf`
  test(heightOf(tree1), 0)
  test(heightOf(tree2), 1)
  test(heightOf(tree3), 2)
  test(heightOf(tree4), 3)
  test(heightOf(tree5), 2)

  // tests for `max`
  test(max(tree1), 8)
  test(max(tree2), 3)
  test(max(tree3), 8)
  test(max(tree4), 8)
  test(max(tree5), 42)

  // tests for `postorder`
  test(postorder(tree1), List(8))
  test(postorder(tree2), List(2, 3, 1))
  test(postorder(tree3), List(5, 8, 3, 2, 4))
  test(postorder(tree4), List(2, 1, 8, 5, 1, 3, 7))
  test(postorder(tree5), List(7, 9, 7, 3, 4, 7, 42))

  // tests for `count`
  test(count(tree1, _ % 2 == 0), 1)
  test(count(tree2, _ % 2 == 1), 2)
  test(count(tree3, _ >= 4), 3)
  test(count(tree4, _ < 5), 4)
  test(count(tree5, _ == 7), 3)

  // tests for `merge`
  test(merge(tree1, tree1), Leaf(16))
  test(merge(tree1, tree2), Leaf(9))
  test(merge(tree2, tree3), Branch(Leaf(7), 5, Leaf(5)))
  test(merge(tree3, tree4), Branch(Leaf(7), 11, Branch(Leaf(13), 5, Leaf(4))))
  test(merge(tree4, tree5), Branch(Leaf(9), 49, Branch(Leaf(8), 10, Leaf(5))))

  // ---------------------------------------------------------------------------
  // Boolean Expressions
  // ---------------------------------------------------------------------------
  import BE.*

  val T = Literal(true)
  val F = Literal(false)
  val X = Variable("x")
  val Y = Variable("y")

  // #t
  val be1: BE = T

  // (x => #f)
  val be2: BE = Imply(X, F)

  // (!(#t || x) && !(y || #f))
  val be3: BE = And(Not(Or(T, X)), Not(Or(Y, F)))

  // ((#t && (x => #f)) || (x => (#t => y)))
  val be4: BE = Or(And(T, Imply(X, F)), Imply(X, Imply(T, Y)))

  // ((!(#t => (x && y)) && (!#f => (#f || x))) => y)
  val be5: BE = Imply(And(Not(Imply(T, And(X, Y))), Imply(Not(F), Or(F, X))), Y)

  // tests for `isImply`
  test(isImply(be1), false)
  test(isImply(be2), true)
  test(isImply(be3), false)
  test(isImply(be4), false)
  test(isImply(be5), true)

  // tests for `noAnd`
  test(noAnd(be1), true)
  test(noAnd(be2), true)
  test(noAnd(be3), false)
  test(noAnd(be4), false)
  test(noAnd(be5), false)

  // tests for `subExprs`
  test(subExprs(be1), Set(T))
  test(subExprs(be2), Set(X, F, be2))
  test(
    subExprs(be3),
    Set(T, F, X, Y, Or(T, X), Or(Y, F), Not(Or(T, X)), Not(Or(Y, F)), be3),
  )
  test(
    subExprs(be4),
    Set(
      T,
      F,
      X,
      Y,
      Imply(X, F),
      Imply(T, Y),
      And(T, Imply(X, F)),
      Imply(X, Imply(T, Y)),
      be4,
    ),
  )
  test(
    subExprs(be5),
    Set(
      T,
      F,
      Y,
      X,
      Not(F),
      Or(F, X),
      And(X, Y),
      Imply(T, And(X, Y)),
      Imply(Not(F), Or(F, X)),
      Not(Imply(T, And(X, Y))),
      And(Not(Imply(T, And(X, Y))), Imply(Not(F), Or(F, X))),
      be5,
    ),
  )

  // tests for `getString`
  test(getString(be1), "#t")
  test(getString(be2), "(x => #f)")
  test(getString(be3), "(!(#t || x) && !(y || #f))")
  test(getString(be4), "((#t && (x => #f)) || (x => (#t => y)))")
  test(getString(be5), "((!(#t => (x && y)) && (!#f => (#f || x))) => y)")

  // tests for `eval`
  val env1: Map[String, Boolean] = Map("x" -> false, "y" -> true)
  val env2: Map[String, Boolean] = Map("x" -> true)
  test(eval(be1, env1), true)
  test(eval(be2, env1), true)
  test(eval(be3, env2), false)
  test(eval(be4, env2), false)
  test(eval(be5, env2), false)

  /* Write your own tests */
}
