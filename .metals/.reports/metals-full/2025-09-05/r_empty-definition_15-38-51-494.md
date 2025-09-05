error id: file:///C:/Users/KIMJH/GitHub/COSE212-2025fall/scala-tutorial/src/main/scala/kuplrg/Implementation.scala:`<none>`.
file:///C:/Users/KIMJH/GitHub/COSE212-2025fall/scala-tutorial/src/main/scala/kuplrg/Implementation.scala
empty definition using pc, found symbol in pc: `<none>`.
empty definition using semanticdb
empty definition using fallback
non-local guesses:
	 -Tree.
	 -Tree#
	 -Tree().
	 -BE.
	 -BE#
	 -BE().
	 -scala/Predef.
	 -scala/Predef#
	 -scala/Predef().
offset: 468
uri: file:///C:/Users/KIMJH/GitHub/COSE212-2025fall/scala-tutorial/src/main/scala/kuplrg/Implementation.scala
text:
```scala
package kuplrg

object Implementation extends Template {

  // ---------------------------------------------------------------------------
  // Basic Data Types
  // ---------------------------------------------------------------------------
  def clamp(lower: Int, x: Int, upper: Int): Int = 
    if x < lower then lower
    else if x > upper then upper
    else x

  def validName(name: String): Boolean =
    if 0 < name.length <= 10 && name(0).isUpper@@Case then true
    else false

  // ---------------------------------------------------------------------------
  // Functions
  // ---------------------------------------------------------------------------
  def collatzLength(n: Int): Int =
    if n == 1 then 1
    else if n%2 == 0 then 1 + collatzLength(n / 2)
    else 1 + collatzLength(3 * n + 1)

  def fixpoint(f: Int => Int): Int => Int = n =>
    if f(n) == n then n
    else fixpoint(f)(f(n))

  def applyK(f: Int => Int, k: Int): Int => Int =
    if k <= 0 then f
    else applyK(f(f), k-1)

  // ---------------------------------------------------------------------------
  // Collections
  // ---------------------------------------------------------------------------
  def sumEven(l: List[Int]): Int = ???

  def double(l: List[Int]): List[Int] = ???

  def generate(f: Int => Int): Int => List[Int] = ???

  def join(l: Map[String, Int], r: Map[String, Int]): Map[String, Int] = ???

  def subsets(set: Set[Int]): List[Set[Int]] = ???

  // ---------------------------------------------------------------------------
  // Trees
  // ---------------------------------------------------------------------------
  import Tree.*

  def heightOf(t: Tree): Int = ???

  def max(t: Tree): Int = ???

  def postorder(t: Tree): List[Int] = ???

  def count(t: Tree, f: Int => Boolean): Int = ???

  def merge(left: Tree, right: Tree): Tree = ???

  // ---------------------------------------------------------------------------
  // Boolean Expressions
  // ---------------------------------------------------------------------------
  import BE.*

  def isImply(expr: BE): Boolean = ???

  def noAnd(expr: BE): Boolean = ???

  def subExprs(expr: BE): Set[BE] = ???

  def getString(expr: BE): String = ???

  def eval(expr: BE, env: Map[String, Boolean]): Boolean = ???
}

```


#### Short summary: 

empty definition using pc, found symbol in pc: `<none>`.