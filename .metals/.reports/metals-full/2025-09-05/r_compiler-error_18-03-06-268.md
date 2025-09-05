file:///C:/Users/KIMJH/GitHub/COSE212-2025fall/scala-tutorial/src/main/scala/kuplrg/Implementation.scala
### java.lang.AssertionError: assertion failed: position not set for nn(<empty>) # -1 of class dotty.tools.dotc.ast.Trees$Apply in C:/Users/KIMJH/GitHub/COSE212-2025fall/scala-tutorial/src/main/scala/kuplrg/Implementation.scala

occurred in the presentation compiler.

presentation compiler configuration:


action parameters:
offset: 2410
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
    if 0 < name.length && name.length <= 10 && 65 <= name(0).toInt && name(0).toInt <= 90 then true
    else false

  // ---------------------------------------------------------------------------
  // Functions
  // ---------------------------------------------------------------------------
  def collatzLength(n: Int): Int =
    if n == 1 then 1
    else if n%2 == 0 then 1 + collatzLength(n / 2)
    else 1 + collatzLength(3 * n + 1)

  def fixpoint(f: Int => Int): Int => Int =
    n =>
      if f(n) == n then n
      else fixpoint(f)(f(n))

  def applyK(f: Int => Int, k: Int): Int => Int =
    n =>
      if k <= 0 then n
      else applyK(f, k-1)(f(n))

  // ---------------------------------------------------------------------------
  // Collections
  // ---------------------------------------------------------------------------
  def sumEven(l: List[Int]): Int =
    l.filter(_ % 2 == 0).sum

  def double(l: List[Int]): List[Int] =
    l.flatMap(x => List(x, x))

  def generate(f: Int => Int): Int => List[Int] =
    n =>
      if f(n) == n then List(n)
      else n :: generate(f)(f(n))

  def join(l: Map[String, Int], r: Map[String, Int]): Map[String, Int] =
    l ++ r.map { case (k, v) => k -> (v + l.getOrElse(k, 0)) }

  def subsets(set: Set[Int]): List[Set[Int]] =
    def hp(set: Set[Int]): List[Set[Int]] = {
      if set.isEmpty then List(Set())
      else {
        val elem = set.max
        val rest = set - elem
        val withoutElem = subsets(rest)
        val withElem = withoutElem.map(s => s + elem)
        withElem ++ withoutElem
      }
    }
    def cmp(a: Set[Int], b: Set[Int]) = {
      val la = a.toList.sorted
      val lb = b.toList.sorted

      val zipped = la.zipAll(lb, Int.MinValue, Int.MinValue)

      zipped.find { case (x, y) => x != y } match {
        case Some((x, y)) => x < y
        case None => la.length < lb.length
      }
    }
    val result = hp(set).filter(_.n@@)
    hp(set).sortWith(cmp)


  // ---------------------------------------------------------------------------
  // Trees
  // ---------------------------------------------------------------------------
  import Tree.*

  def heightOf(t: Tree): Int =
    t match {
      case Leaf(_) => 0
      case Branch(l, _, r) => {
        if heightOf(l) > heightOf(r) then 1 + heightOf(l) else 1 + heightOf(r)
      }
    }

  def max(t: Tree): Int =
    t match {
      case Leaf(v) => v
      case Branch(l, v, r) => {
        Math.max(v, Math.max(max(l), max(r)))
      }
    }

  def postorder(t: Tree): List[Int] =
    t match {
      case Leaf(v) => List(v)
      case Branch(l, v, r) => postorder(l) ++ postorder(r) ++ List(v)
    }

  def count(t: Tree, f: Int => Boolean): Int =
    t match {
      case Leaf(v) => if f(v) then 1 else 0
      case Branch(l, v, r) => {
        if f(v) then 1 + count(l, f) + count(r, f)
        else count(l, f) + count(r, f)
      }
    }

  def merge(left: Tree, right: Tree): Tree =
    (left, right) match {
      case (Leaf(v1), Leaf(v2)) => Leaf(v1 + v2)
      case (Branch(l1, v1, r1), Branch(l2, v2, r2)) =>
        Branch(merge(l1, l2), v1 + v2, merge(r1, r2))
      case (Branch(l, v, r), Leaf(v2)) =>
        Leaf(v + v2)
      case (Leaf(v1), Branch(l, v, r)) =>
        Leaf(v1 + v)
    }

  // ---------------------------------------------------------------------------
  // Boolean Expressions
  // ---------------------------------------------------------------------------
  import BE.*

  def isImply(expr: BE): Boolean =
    expr match {
      case Imply(_, _) => true
      case _ => false
    }

  def noAnd(expr: BE): Boolean =
    expr match {
      case And(_, _) => false
      case Literal(_) | Variable(_) => true
      case Not(e) => noAnd(e)
      case Imply(l, r) => noAnd(l) && noAnd(r)
      case Or(l, r) => noAnd(l) && noAnd(r)
    }

  def subExprs(expr: BE): Set[BE] =
    expr match {
      case Literal(_) | Variable(_) => Set(expr)
      case Not(e) => Set(expr) ++ subExprs(e)
      case Or(l, r) => Set(expr) ++ subExprs(l) ++ subExprs(r)
      case And(l, r) => Set(expr) ++ subExprs(l) ++ subExprs(r)
      case Imply(l, r) => Set(expr) ++ subExprs(l) ++ subExprs(r)
    }

  def getString(expr: BE): String =
    expr match {
      case Literal(true) => "#t"
      case Literal(false) => "#f"
      case Variable(name) => name
      case Not(e) => "!" + getString(e) + ""
      case Or(l, r) => "(" + getString(l) + " || " + getString(r) + ")"
      case And(l, r) => "(" + getString(l) + " && " + getString(r) + ")"
      case Imply(l, r) => "(" + getString(l) + " => " + getString(r) + ")"
    }

  def eval(expr: BE, env: Map[String, Boolean]): Boolean =
    expr match {
      case Literal(v) => v
      case Variable(name) => if env contains name then env(name) else false
      case Not(e) => !eval(e, env)
      case Or(l, r) => eval(l, env) || eval(r, env)
      case And(l, r) => eval(l, env) && eval(r, env)
      case Imply(l, r) => !eval(l, env) || eval(r, env)
    }
}
```



#### Error stacktrace:

```
scala.runtime.Scala3RunTime$.assertFailed(Scala3RunTime.scala:8)
	dotty.tools.dotc.typer.Typer$.assertPositioned(Typer.scala:72)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3297)
	dotty.tools.dotc.typer.Applications.extMethodApply(Applications.scala:2483)
	dotty.tools.dotc.typer.Applications.extMethodApply$(Applications.scala:400)
	dotty.tools.dotc.typer.Typer.extMethodApply(Typer.scala:119)
	dotty.tools.dotc.typer.Applications.tryApplyingExtensionMethod(Applications.scala:2528)
	dotty.tools.dotc.typer.Applications.tryApplyingExtensionMethod$(Applications.scala:400)
	dotty.tools.dotc.typer.Typer.tryApplyingExtensionMethod(Typer.scala:119)
	dotty.tools.dotc.interactive.Completion$Completer.tryApplyingReceiverToExtension$1(Completion.scala:526)
	dotty.tools.dotc.interactive.Completion$Completer.$anonfun$23(Completion.scala:569)
	scala.collection.immutable.List.flatMap(List.scala:294)
	scala.collection.immutable.List.flatMap(List.scala:79)
	dotty.tools.dotc.interactive.Completion$Completer.extensionCompletions(Completion.scala:566)
	dotty.tools.dotc.interactive.Completion$Completer.selectionCompletions(Completion.scala:446)
	dotty.tools.dotc.interactive.Completion$.computeCompletions(Completion.scala:218)
	dotty.tools.dotc.interactive.Completion$.rawCompletions(Completion.scala:78)
	dotty.tools.pc.completions.Completions.enrichedCompilerCompletions(Completions.scala:114)
	dotty.tools.pc.completions.Completions.completions(Completions.scala:136)
	dotty.tools.pc.completions.CompletionProvider.completions(CompletionProvider.scala:139)
	dotty.tools.pc.ScalaPresentationCompiler.complete$$anonfun$1(ScalaPresentationCompiler.scala:150)
```
#### Short summary: 

java.lang.AssertionError: assertion failed: position not set for nn(<empty>) # -1 of class dotty.tools.dotc.ast.Trees$Apply in C:/Users/KIMJH/GitHub/COSE212-2025fall/scala-tutorial/src/main/scala/kuplrg/Implementation.scala