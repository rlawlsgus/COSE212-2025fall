package kuplrg

trait Template {

  // ---------------------------------------------------------------------------
  // Basic Data Types
  // ---------------------------------------------------------------------------
  def clamp(lower: Int, x: Int, upper: Int): Int

  def validName(name: String): Boolean

  // ---------------------------------------------------------------------------
  // Functions
  // ---------------------------------------------------------------------------
  def collatzLength(n: Int): Int

  def fixpoint(f: Int => Int): Int => Int

  def applyK(f: Int => Int, k: Int): Int => Int

  // ---------------------------------------------------------------------------
  // Collections
  // ---------------------------------------------------------------------------
  def sumEven(l: List[Int]): Int

  def double(l: List[Int]): List[Int]

  def generate(f: Int => Int): Int => List[Int]

  def join(l: Map[String, Int], r: Map[String, Int]): Map[String, Int]

  def subsets(set: Set[Int]): List[Set[Int]]

  // ---------------------------------------------------------------------------
  // Trees
  // ---------------------------------------------------------------------------
  enum Tree:
    case Leaf(value: Int)
    case Branch(left: Tree, value: Int, right: Tree)

  def heightOf(t: Tree): Int

  def max(t: Tree): Int

  def postorder(t: Tree): List[Int]

  def count(t: Tree, f: Int => Boolean): Int

  def merge(left: Tree, right: Tree): Tree

  // ---------------------------------------------------------------------------
  // Boolean Expressions
  // ---------------------------------------------------------------------------
  enum BE:
    case Literal(bool: Boolean)
    case Variable(name: String)
    case And(left: BE, right: BE)
    case Or(left: BE, right: BE)
    case Imply(left: BE, right: BE)
    case Not(expr: BE)

  def isImply(expr: BE): Boolean

  def noAnd(expr: BE): Boolean

  def subExprs(expr: BE): Set[BE]

  def getString(expr: BE): String

  def eval(expr: BE, env: Map[String, Boolean]): Boolean
}
