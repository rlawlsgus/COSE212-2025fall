package kuplrg

import Implementation.*

class Spec extends SpecBase {

  test(eval("None"), "None")
  test(eval("42"), "42")
  test(eval("True"), "True")
  test(eval("False"), "False")
  test(eval("x = 1; x"), "1")
  testExc(eval("x"), "NameError: x")
  test(eval("x = y; y = 1; x"), "None")
  test(eval("-(-42)"), "42")
  test(eval("1 + 2"), "3")
  testExc(eval("1 + True"), "TypeError")
  test(eval("19 - 2"), "17")
  test(eval("2 * 3"), "6")
  test(eval("17 // 5"), "3")
  test(eval("15 // -5"), "-3")
  test(eval("17 // -5"), "-3")
  testExc(eval("3 // 0"), "ZeroDivisionError")
  test(eval("17 % 5"), "2")
  test(eval("15 % -5"), "0")
  test(eval("17 % -5"), "2")
  testExc(eval("3 % 0"), "ZeroDivisionError")
  test(eval("not True"), "False")
  test(eval("not False"), "True")
  test(eval("not []"), "True")
  test(eval("not [1]"), "False")
  test(eval("not None"), "True")
  test(eval("not 42"), "False")
  test(eval("not 0"), "True")
  test(eval("not (lambda: x)"), "False")
  test(eval("True and True"), "True")
  test(eval("True and False"), "False")
  test(eval("True and 42"), "42")
  test(eval("False and True"), "False")
  test(eval("False and False"), "False")
  test(eval("True or True"), "True")
  test(eval("True or False"), "True")
  test(eval("False or 42"), "42")
  test(eval("False or True"), "True")
  test(eval("False or False"), "False")
  test(eval("1 == 1"), "True")
  test(eval("1 == 2"), "False")
  test(eval("True == True"), "True")
  test(eval("True == 42"), "False")
  test(eval("True == 1"), "False")
  test(eval("False == False"), "True")
  test(eval("False == 0"), "False")
  test(eval("False == 42"), "False")
  test(eval("True == False"), "False")
  test(eval("None == None"), "True")
  testExc(eval("None < 1"), "TypeError")
  test(eval("(lambda: x) == (lambda: x)"), "False")
  test(eval("f = (lambda: x); g = f; f == g"), "True")
  test(eval("[1,2,3] == [1,2,3]"), "True")
  test(eval("[1,2,3] == [1,2,4]"), "False")
  test(eval("1 != 1"), "False")
  test(eval("1 < 2"), "True")
  test(eval("2 >= 5"), "False")
  test(eval("1 > 1"), "False")
  test(eval("1 <= 1"), "True")
  testExc(eval("1 < True"), "TypeError")
  testExc(eval("1 <= True"), "TypeError")
  testExc(eval("False < 1"), "TypeError")
  test(eval("[1, 2] < [1, 2, 3]"), "True")
  test(eval("[1, 3] < [1, 2, 3]"), "False")
  test(eval("[1, 2, 4] < [1, 3]"), "True")
  testExc(eval("[] < 1"), "TypeError")
  test(eval("1 is 1"), "True")
  test(eval("1 is True"), "False")
  test(eval("1 is 2"), "False")
  test(eval("[1, 2, 3] is [1, 2, 3]"), "False")
  test(eval("x = [1, 2, 3]; y = x; x is y"), "True")
  test(eval("(lambda: x) is (lambda: x)"), "False")
  test(eval("f = (lambda: x); g = f; f is g"), "True")
  test(eval("None is None"), "True")
  test(eval("[1,2,3].append(4)"), "[1, 2, 3, 4]")
  test(eval("x = [1,2,3]; x.append(4); x"), "[1, 2, 3, 4]")
  test(eval("x = [1,2,3]; x.append(4).append(5); x"), "[1, 2, 3, 4, 5]")
  testExc(eval("42.append(4)"), "TypeError")
  test(eval("[1,2,3][0]"), "1")
  test(eval("[1,2,3][1]"), "2")
  test(eval("[1,2,3][-1]"), "3")
  test(eval("[1,2,3][-3]"), "1")
  test(eval("[1,2,3][1 + 1]"), "3")
  testExc(eval("[][0]"), "IndexError")
  testExc(eval("[1,2,3][3]"), "IndexError")
  testExc(eval("[1,2,3][-4]"), "IndexError")
  test(eval("lambda x: x"), "<clo>")
  test(eval("(lambda x: x + 1)(2)"), "3")
  test(eval("(lambda x, y: x - y)(2, 5)"), "-3")
  test(eval("(lambda x: x)(42)"), "42")
  test(eval("(lambda x: lambda y: x + y)(1)(2)"), "3")
  testExc(eval("1(2)"), "TypeError")
  test(eval("10 if 3 < 5 else 20"), "10")
  test(eval("10 if 3 > 5 else 20"), "20")
  test(eval("10 if 3 < 5 else 1 + True"), "10")
  test(eval("1 // 0 if 3 > 5 else 20"), "20")
  test(eval("10 if 3 else 20"), "10")
  test(eval("10 if [] else 20"), "20")
  test(eval("10 if [1] else 20"), "10")
  test(eval("10 if None else 20"), "20")
  test(eval("10 if (lambda: x) else 20"), "10")
  test(eval("iter([1, 2, 3])"), "<iter>")
  test(eval("x = iter([1, 2, 3]); x is iter(x)"), "True")
  testExc(eval("iter(42)"), "TypeError")
  test(eval("x = iter([1, 2]); next(x)"), "1")
  test(eval("x = iter([1, 2]); next(x); next(x)"), "2")
  testExc(eval("x = iter([1, 2]); next(x); next(x); next(x)"), "StopIteration")
  test(eval("pass; 42"), "42")
  test(eval("1; 2"), "2")
  test(eval("x = 2; x = x + 1; x"), "3")
  test(eval("def f(): pass\nf()"), "None")
  test(eval("x = 1\ndef f(): x = 2\nf()\nx"), "1")
  test(eval("x = [1, 2, 3]; x[0] = 7; x"), "[7, 2, 3]")
  test(eval("x = [1, 2, 3]; x[-1] = 7; x"), "[1, 2, 7]")
  testExc(eval("x = [1, 2, 3]; x[3] = 7; x"), "IndexError")
  testExc(eval("x = [1, 2, 3]; x[-4] = 7; x"), "IndexError")
  testExc(eval("1[2] = 3; 1"), "TypeError")
  test(eval("if True: x = 1\nelse: x = 2\nx"), "1")
  test(eval("if False: x = 1\nelse: x = 2\nx"), "2")
  test(eval("if 0: x = 1\nelif 1: x = 2\nelse: x = 3\nx"), "2")
  test(eval("while (False): x\n42"), "42")
  test(eval("x = 0\nwhile x < 3: x = x + 1\nx"), "3")
  test(eval("x = 0\nwhile 1:\n  if x>1: break\n  else: x = x + 1\nx"), "2")
  test(eval("x = 0\nwhile x < 3: x = x + 1; continue; x = 0\nx"), "3")
  testExc(eval("raise; 42"), "RuntimeError")
  test(eval("try: x = 1\nexcept: x = 2\nx"), "1")
  test(eval("try: x = 1; raise; x = 2\nexcept: y = x\ny"), "1")
  test(eval("try: x\nexcept: y = 1\ny"), "1")
  test(eval("try: 1 // 0\nexcept: x = 42\nx"), "42")
  test(eval("try: 1(2)\nexcept: x = 42\nx"), "42")
  test(eval("def f(x): return x - 1; 42\nf(5)"), "4")
  test(eval("def f(n):\n  if n: return n + f(n - 1)\n  return 0\nf(10)"), "55")
  test(eval("def f(): raise\ntry: x = 1; f(); x = 2\nexcept: y = x\ny"), "1")
  test(eval("def f(): yield 42\nf"), "<gen>")
  test(eval("def f(): yield 42\nf()"), "<iter>")
  test(eval("def f(): yield 1; yield 2\nx = f(); next(x)"), "1")
  test(eval("def f(): yield 1; yield 2\nx = f(); next(x); next(x)"), "2")
  testExc(eval("def f(): return 42; yield 1\nnext(f())"), "StopIteration")
  testExc(eval("def f(): yield 1\nx = f();next(x);next(x)"), "StopIteration")
  test(eval("s = 0\nfor x in [1, 3, 5, 7, 9]: s = s + x\ns"), "25")
  test(
    eval("""
def f(x):
  while x:
    yield x
    x = x - 1
sum = 0
for x in f(10):
  sum = sum + x
sum
"""),
    "55",
  )

  // Helper functions
  // -------------------------------------------------------------------------
  val rangeDef = """
def range(start, stop, step):
  if stop is None: stop = start; start = 0
  if step == 0: raise
  i = start
  if 0 < step: 
    while i < stop: yield i; i = i + step
  else:
    while i > stop: yield i; i = i + step
"""

  val lenDef = """
def len(iterable):
  result = 0
  for x in iterable: result = result + 1
  return result
"""

  val sumDef = """
def sum(iter):
  result = 0
  for x in iter: result = result + x
  return result
"""

  val takeDef = """
def take(iter, n):
  i = 0
  for x in iter:
    if n <= i: break
    yield x
    i = i + 1
"""

  val listDef = """
def list(iterable):
  result = []
  if iterable is not None:
    for item in iterable:
      result.append(item)
  return result
"""

  val flattenDef = """
def flatten(xs):
  for x in xs:
    try:
      iter(x)
      yield from flatten(x)
    except:
      yield x
"""

  val filterDef = """
def filter(pred, iterable):
  for x in iterable:
    if pred(x): yield x
"""

  val mapDef = """
def map(func, iterable):
  for x in iterable: yield func(x)
"""

  // More tests
  // -------------------------------------------------------------------------
  val expr1 = s"""
x = 10
sum = 0
while 0 < x: sum = sum + x; x = x - 1
sum
"""
  test(eval(expr1), "55", weight = 3) // 10 + 9 + ... + 1 = 55

  val expr2 = s"""
def factorial(n):
  result = 1
  while n > 0:
    result = result * n
    n = n - 1
  return result
factorial(5)
"""
  test(eval(expr2), "120", weight = 3) // 5 * 4 * 3 * 2 * 1 = 120

  val expr3 = s"""
def collatzCount(n):
  count = 0
  while (n > 1):
    if n % 2 == 0: n = n // 2
    else: n = 3 * n + 1
    count = count + 1
  return count
collatzCount(27)
"""
  test(eval(expr3), "111", weight = 3) // 27 -> 82 -> ... -> 2 -> 1 (111 steps)

  val expr4 = s"""
def nats():
  n = 0
  while (True): yield n; n = n + 1
iter = nats()
next(iter)
next(iter)
next(iter)
"""
  test(eval(expr4), "2", weight = 3)

  val expr5 = s"""
def outer():
  x = 0
  def inner():
    x = x     # x is None
    return x
  return inner

f = outer()
f()
"""
  test(eval(expr5), "None", weight = 3)

  val expr6 = s"""
$rangeDef
list = []
for i in range(3, None, 1):
  def f(): return i     # Captures i by reference
  list.append(f)

for j in range(3, None, 1):
  list[j] = list[j]()

list
"""
  test(eval(expr6), "[2, 2, 2]", weight = 3)

  val expr7 = s"""
$rangeDef
list = [0, 0, 0]
for i in range(3, None, 1):
  f = (lambda j: (lambda: j))(i)    # Captures i with a lambda parameter
  list[i] = f

for j in range(3, None, 1):
  list[j] = list[j]()

list
"""
  test(eval(expr7), "[0, 1, 2]", weight = 3)

  val expr8 = s"""
def outer(flag):
  if flag:
    x = 42         # x will not be defined if flag is False

  def inner():
    return x       # if flag is False, x is None

  return inner()

outer(False)
"""
  test(eval(expr8), "None", weight = 3)

  val expr9 = s"""
def f():
  x = 7
  def g():
    def h():
      return x    # x is not yet assigned, so it is None
    if False: x = 42
    return h()    # calling h() before defining x in g()
  return g()
f()
"""
  test(eval(expr9), "None", weight = 3)

  val expr10 = s"""
def f():
  x = 7
  def g():
    def h():
      return x    # x is 42
    if True: x = 42
    return h()    # calling h() after defining x in g()
  return g()
f()
"""
  test(eval(expr10), "42", weight = 3)

  val expr11 = s"""
$rangeDef
def sum(iter):
  result = 0
  for x in iter: result = result + x
  return result
sum(range(6, 15, 1))
"""
  test(eval(expr11), "90", weight = 3) // 6 + 7 + 8 + ... + 13 + 14 = 90

  val expr12 = s"""
$rangeDef
$sumDef
def squares(n):
  for x in range(1, n + 1, 1):
    yield x * x
sum(squares(10))
"""
  test(eval(expr12), "385", weight = 3) // 1^2 + 2^2 + ... + 9^2 + 10^2 = 385

  val expr13 = s"""
$rangeDef
$sumDef
def fibonacci(n):
  a = 0
  b = 1
  for x in range(n, None, 1):
    tmp = a
    a = b
    b = b + tmp
    yield a
sum(fibonacci(10))
"""
  test(eval(expr13), "143", weight = 3) // 1 + 1 + 2 + 3 + ... + 34 + 55 = 143

  val expr14 = s"""
$rangeDef
$takeDef
$sumDef
sum(take(range(1, 1000, 1), 10))
"""
  test(eval(expr14), "55", weight = 3) // 1 + 2 + ... + 9 + 10 = 55

  val expr15 = s"""
$rangeDef
$takeDef
$listDef
list(range(20, 1, -3))
"""
  test(eval(expr15), "[20, 17, 14, 11, 8, 5, 2]", weight = 3)

  val expr16 = s"""
$rangeDef
$takeDef
$listDef
def isPrime(n):
  for x in range(2, n, 1):
    if n % x == 0: return False
    if x * x > n: break
  return True
def allPrimes():
  n = 2
  while (True):
    if isPrime(n): yield n
    n = n + 1
list(take(allPrimes(), 10))
"""
  test(eval(expr16), "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]", weight = 3)

  val expr17 = s"""
$rangeDef
$listDef
$flattenDef
list(flatten([1, [2, 3], range(4, 6, 1), [[7], 8], range(3, 2, 1), 9, [[]]]))
"""
  test(eval(expr17), "[1, 2, 3, 4, 5, 7, 8, 9]", weight = 3)

  val expr18 = s"""
$rangeDef
$filterDef
$takeDef
$listDef
def isPrime(n):
  for x in range(2, n, 1):
    if n % x == 0: return False
    if x * x > n: break
  return True
def allPrimes():
  n = 2
  while (True):
    if isPrime(n): yield n
    n = n + 1
list(take(filter(lambda x: x % 10 == 7, allPrimes()), 10))
"""
  test(eval(expr18), "[7, 17, 37, 47, 67, 97, 107, 127, 137, 157]", weight = 3)

  val expr19 = s"""
$rangeDef
$listDef
$filterDef
$mapDef
$sumDef
ranges = map(lambda x: list(range(x + 1, None, 1)), range(10, None, 1))
filtered = filter(lambda y: sum(y) % 3 == 0, ranges)
list(map(lambda z: z[-1], filtered))
"""
  test(eval(expr19), "[0, 2, 3, 5, 6, 8, 9]", weight = 3)

  val expr20 = s"""
$lenDef
$listDef
def powerset(xs):
  xs = list(xs)
  def go(i):
    if i < 0:
      yield []
    else:
      for s in go(i - 1): yield s
      for s in go(i - 1): yield list(s).append(xs[i])
  yield from go(len(xs) - 1)

list(powerset([2,5,7]))
"""
  test(
    eval(expr20),
    "[[], [2], [5], [2, 5], [7], [2, 7], [5, 7], [2, 5, 7]]",
    weight = 3,
  )

  /* Write your own tests */
}
