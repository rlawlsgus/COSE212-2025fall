package kuplrg

import Implementation.*

class Spec extends SpecBase {

  // -------------------------------------------------------------------------
  // Problem #1: interp
  // -------------------------------------------------------------------------
  test(eval("42"), "42")
  test(eval("true"), "true")
  test(eval("false"), "false")
  testExc(eval("x"), "free identifier")
  test(eval("-(-42)"), "42")
  test(eval("1 + 2"), "3")
  test(eval("19 - 2"), "17")
  test(eval("2 * 3"), "6")
  test(eval("15 / 2"), "7")
  testExc(eval("3 / 0"), "invalid operation")
  test(eval("15 % -4"), "3")
  testExc(eval("3 % 0"), "invalid operation")
  test(eval("!true"), "false")
  test(eval("!false"), "true")
  test(eval("true && true"), "true")
  test(eval("true && false"), "false")
  test(eval("false && true"), "false")
  test(eval("false && false"), "false")
  test(eval("true || true"), "true")
  test(eval("true || false"), "true")
  test(eval("false || true"), "true")
  test(eval("false || false"), "false")
  test(eval("1 = 1"), "true")
  test(eval("1 = 2"), "false")
  test(eval("1 <> 1"), "false")
  test(eval("true = 1"), "false")
  test(eval("true = true"), "true")
  test(eval("true = false"), "false")
  test(eval("[] = []"), "true")
  test(eval("[] = (1 :: [])"), "false")
  test(eval("(2 :: []) = []"), "false")
  testExc(eval("1 :: 2"), "not a list")
  test(eval("[1; 2; 3] = 1 :: 2 :: 3 :: []"), "true")
  test(eval("(1, 2, true) = (1, 2, true)"), "true")
  test(eval("(fun x -> x + 1) <> 42"), "true")
  test(eval("(fun x -> x + 1) = (fun x -> x + 1)"), "false")
  test(eval("(1, fun x -> x) = (1, fun x -> x)"), "false")
  test(eval("[1; 2; (fun x -> x); 5] = [1; 2; (fun x -> x); 5]"), "false")
  test(eval("(fun x -> x) :: [] = (fun x -> x) :: []"), "false")
  test(eval("(1, 2, 3) <> [1; 2; 3]"), "true")
  test(eval("1 < 2"), "true")
  test(eval("2 >= 5"), "false")
  test(eval("1 <= 1"), "true")
  test(eval("1 > 1"), "false")
  testExc(eval("1 < true"), "invalid operation")
  test(eval("if 3 < 5 then 10 else 20"), "10")
  test(eval("if 3 > 5 then 10 else 20"), "20")
  test(eval("if 3 < 5 then 10 else 1 + true"), "10")
  test(eval("if 3 > 5 then 1 + true else 20"), "20")
  testExc(eval("if 3 then 10 else 20"), "not a boolean")
  test(eval("[]"), "[]")
  test(eval("1 :: 2 :: 3 :: []"), "[1; 2; 3]")
  test(eval("[4; 2; 3]"), "[4; 2; 3]")
  test(eval("let x = 42 in x + 1"), "43")
  test(eval("let x = 1 in let y = 2 in x + y"), "3")
  test(eval("let (x, y) = (1, 2) in x + y"), "3")
  testExc(eval("let (x, y, z) = 42 in x"), "invalid pattern match")
  test(eval("let (1, y) = (1, 2) in y"), "2")
  testExc(eval("let (1, y) = (2, 3) in y"), "invalid pattern match")
  test(eval("let h :: _ = [1; 2; 3] in h"), "1")
  test(eval("let [x; y] = [1; 2] in x + y"), "3")
  testExc(eval("let [x; y] = [1; 2; 3] in x + y"), "invalid pattern match")
  test(eval("(let x = 1 in x) + (let y = 2 in y)"), "3")
  testExc(eval("(let x = 42 in x + 1) + x"), "free identifier")
  test(eval("fun x -> x + 1"), "<function>")
  test(eval("fun () -> x"), "<function>")
  test(eval("(fun x -> x + 2) 3"), "5")
  test(eval("let addN n m = n + m in let add3 = addN 3 in add3 4"), "7")
  test(eval("let g = fun () -> 1 + 2 in g ()"), "3")
  test(eval("let f = fun (a, b, c) -> a + b + c in f (1, 2, 3)"), "6")
  test(eval("let x = 42 in let f = fun y -> x + y in let x = 3 in f 1"), "43")
  testExc(eval("42 true"), "not a function")
  test(eval("let rec f x y = x + y in f 1"), "<function>")
  test(eval("let rec g y = f (y + 1) and f x = x * 2 in g 3"), "8")
  test(eval("let f x = match x with | 0 -> 0 | _ -> 1 in f 0"), "0")
  test(eval("let f x = match x with | 0 -> 0 | _ -> 1 in f 42"), "1")
  test(eval("let f x = match x with | 0 -> 0 | _ -> 1 in f true"), "1")
  test(eval("let f x = match x with | 0 -> 0 | _ -> y in f 0"), "0")
  test(eval("let f x = match x with | 0 -> 0 | 0 -> 1 in f 0"), "0")
  testExc(eval("let f x = match x with | 0 -> 0 in f 42"), "unmatched value")
  testExc(eval("let f x = match x with | true -> -1 in f 0"), "unmatched value")
  test(
    eval("let f opt = match opt with | None -> 0 | Some x -> x in f (Some 42)"),
    "42",
  )
  test(
    eval("let rec sum x = if x < 1 then 0 else x + sum (x - 1) in sum 10"),
    "55",
  )
  test(
    eval("let rec mod(x, y) = if x < y then x else mod(x-y, y) in mod(42, 5)"),
    "2",
  )
  test(
    eval("""
    let rec len l =
      match l with 
      | [] -> 0
      | _ :: t -> 1 + len t
    in len [1;2;3]"""),
    "3",
  )
  test(
    eval("""
      let rec len l =
        match l with 
        | [] -> 0
        | _ :: t -> 1 + len t
      in len [1;2;3]
    """),
    "3",
    weight = 5,
  )
  test(
    eval("""
      let rec alternate l1 l2 =
        match l1, l2 with
        | ([], _) -> l2
        | (_, []) -> l1
        | h1 :: t1, h2 :: t2 -> h1 :: h2 :: alternate t1 t2
      in alternate [1; 2; 3] [4; 5; 6]
    """),
    "[1; 4; 2; 5; 3; 6]",
    weight = 5,
  )
  test(
    eval("""
      let rec flatten l =
        let rec aux l1 l2 =
          match l1 with
          | [] -> l2
          | h :: t -> h :: aux t l2
        in match l with
        | [] -> []
        | h :: t -> aux h (flatten t)
      in flatten [[1; [2; 3]]; [4]; [5; 6]]
    """),
    "[1; [2; 3]; 4; 5; 6]",
    weight = 5,
  )
  val expr1 = """
    let rec gcd a b = if a = 0 then b else gcd (b % a) a
    in gcd 432 180
  """
  test(eval(expr1), "36", weight = 5)
  val expr2 = """
    let rec fact n = if  n > 0 then n * fact (n - 1) else 1
    in fact 10
  """
  test(eval(expr2), "3628800", weight = 5)
  val expr3 = """
    let rec isPrime n =
      let rec iter k =
        if k * k > n then true
        elif n % k = 0 then false
        else iter (k + 1)
      in if n < 2 then false else iter 2
    in isPrime 1000003
  """
  test(eval(expr3), "true", weight = 5)
  val expr4 = """
    let rec sum n =
      let rec iter k acc =
        if k > n then acc
        else iter (k + 1) (acc + k)
      in iter 1 0
    in sum 100
  """
  test(eval(expr4), "5050", weight = 5)
  val expr5 = """
    let rec findKth f k =
      let rec iter n k =
        if f n then
          if k = 1 then n
          else iter (n + 1) (k - 1)
        else iter (n + 1) k
      in iter 0 k
    in findKth (fun x -> x % 3 = 2) 43
  """
  test(eval(expr5), "128", weight = 5)
  val expr6 = """
    let rec isPrime n =
      let rec iter k =
        if k * k > n then true
        elif n % k = 0 then false
        else iter (k + 1)
      in if n < 2 then false else iter 2
    and findKth f k =
      let rec iter n k =
        if f n then
          if k = 1 then n
          else iter (n + 1) (k - 1)
        else iter (n + 1) k
      in iter 0 k
    in findKth isPrime 101
  """
  test(eval(expr6), "547", weight = 5)
  val expr7 = """
    let rec addN n x = x + n
    and isEven x = x % 2 = 0
    and findKth f k =
      let rec iter n k =
        if f n then
          if k = 1 then n
          else iter (n + 1) (k - 1)
        else iter (n + 1) k
      in iter 0 k
    in findKth (fun n -> isEven (addN n 1)) 23
  """
  test(eval(expr7), "45", weight = 5)
  val expr8 = """
    let rec sum n map filter =
      let rec iter k acc =
        if k > n then acc
        else iter (k + 1) (acc + (if filter k then map k else 0))
      in iter 1 0
    in sum 10 (fun x -> x * x) (fun x -> x % 2 = 1)
  """
  test(eval(expr8), "165", weight = 5)
  val expr9 = """
    let rec isEven x = x = 0 || if x > 0 then isOdd (x - 1) else isOdd (x + 1)
    and isOdd x = if x > 0 then isEven (x - 1) else isEven (x + 1)
    in isEven 532
  """
  test(eval(expr9), "true", weight = 5)
  val expr10 = """
    let rec isPrime n =
      let rec aux k =
        if k * k > n then true
        elif n % k = 0 then false
        else aux (k + 1)
      in if n < 2 then false else aux 2
    and factorize n =
      if isPrime n then [n]
      else
        let rec aux m =
          if n % m = 0 then m :: factorize (n / m)
          else aux (m + 1)
        in aux 2
    in factorize 936
  """
  test(eval(expr10), "[2; 2; 2; 3; 3; 13]", weight = 5)
  val expr11 = """
    let mkRec body =
      let fX fY =
        let f = fun x -> fY fY x
        in body f
      in fX(fX)
    in let sum = mkRec (fun sum n ->
      if n < 1 then 0
      else n + sum (n - 1)
    )
    in sum(10)
  """
  test(eval(expr11), "55", weight = 5)
  val expr12 = """
    let mkRec body =
      let fX fY =
        let f = fun x -> fY fY x
        in body f
      in fX(fX)
    in let fac = mkRec(fun fac n -> if n < 1 then 1 else n * fac (n - 1))
    in fac 10
  """
  test(eval(expr12), "3628800", weight = 5)
  val expr13 = """
    let safeHead l =
      match l with
      | [] -> None
      | h :: _ -> Some h
    in (safeHead [1; 2; 3], safeHead [])
  """
  test(eval(expr13), "((Some 1), None)", weight = 5)
  val expr14 = """
    let rec merge xs ys =
      match xs, ys with
      | [], ys -> ys
      | xs, [] -> xs
      | x :: xt, y :: yt ->
        if x <= y then x :: merge xt ys
        else y :: merge xs yt
    in merge [1; 3; 4; 7] [2; 5; 6; 8]
  """
  test(eval(expr14), "[1; 2; 3; 4; 5; 6; 7; 8]", weight = 5)
  val expr15 = """
    let rec derivative poly =
      match poly with
      | [] -> []
      | (a, n) :: t ->
          let term = if n = 0 then None else Some (a * n, n - 1)
          in match term with
          | Some v -> v :: derivative t
          | None -> derivative t
    in derivative [ (3,3); (2,1); (5,0) ]
  """
  test(eval(expr15), "[(9, 2); (2, 0)]", weight = 5)
  val expr16 = """
    let rec inc number counts =
      match counts with
      | [] -> [number, 1]
      | (w, c) :: t ->
        if w = number then (w, c + 1) :: t
        else (w, c) :: inc number t
      | h :: t -> h :: inc number t
    and numberFreq numbers =
      let rec go ws acc =
        match ws with
        | [] -> acc
        | w :: t -> go t (inc w acc)
      in go numbers []
    in numberFreq [42; 13; 42; 7; 13; 42; 7; 42; 7]
  """
  test(eval(expr16), "[(42, 4); (13, 2); (7, 3)]", weight = 5)
  val expr17 = """
    let rec min x y = if x < y then x else y
    and max x y = if x > y then x else y
    and minMax xs =
      match xs with
      | [] -> None
      | [x] -> Some (x, x)
      | h :: t ->
          match minMax t with
          | Some (mn, mx) -> Some (min h mn, max h mx)
          | None -> Some (h, h)
  in (minMax [5; 2; 8; 1; 9], minMax [])
  """
  test(eval(expr17), "((Some (1, 9)), None)", weight = 5)
  val expr18 = """
    let abs = fun x -> if x < 0 then -x else x in

    let rec len list =
      match list with
      | [] -> 0
      | _ :: t -> 1 + len t in

    let rec rev list =
      let rec aux list acc =
        match list with
        | [] -> acc
        | h :: t -> aux t (h :: acc) in
      aux list [] in

    let rec append a b =
      match a with
      | [] -> b
      | h :: t -> h :: append t b in

    let collect f xs =
      let rec loop xs acc =
        match xs with
        | [] -> rev acc
        | h :: t ->
          let mapped = f h in
          loop t (append (rev mapped) acc) in
      loop xs [] in

    let rec range m n =
      if m > n then []
      else m :: range (m + 1) n in

    let rec safe col cols delta =
      match cols with
      | [] -> true
      | c :: rest ->
        (col <> c) &&
        (abs (col - c) <> delta) &&
        safe col rest (delta + 1) in

    let rec place n row partial =
      if row = n then [rev partial]
      else
        let f = fun col ->
          if safe col partial 1 then place n (row+1) (col :: partial)
          else [] in
        collect f (range 0 (n - 1)) in
            
    let solutionsNQueens n = place n 0 [] in

    len (solutionsNQueens 8)
  """
  test(eval(expr18), "92", weight = 5)
  val expr19 = """
    let inc x = x + 1 in

    let rec map f list =
      match list with
      | [] -> []
      | h :: t -> f h :: map f t in

    let rec knap items cap =
      match items, cap with
      | [], _ -> (0, [])
      | (v, w) :: rest, c ->
        if c <= 0 then (0, [])
        else
          let (v0, is0) = knap rest c in
          if w > c then (v0, is0)
          else
            let (v1, is1) = knap rest (c - w) in
            if v1 + v > v0 then (v1 + v, 0 :: map inc is1)
            else (v0, map inc is0) in

    let items = [ (60,10); (100,20); (120,30) ] in
    map (knap items) [10; 20; 30; 40; 50]
  """
  test(
    eval(expr19),
    "[" +
    "(60, [0]); " +
    "(100, [1]); " +
    "(160, [0; 1]); " +
    "(180, [0; 2]); " +
    "(220, [1; 2])"
    + "]",
    weight = 5,
  )
  val expr20 = """
    let rec map f list =
      match list with
      | [] -> []
      | h :: t -> f h :: map f t in

    let rec rev list =
      let rec aux list acc =
        match list with
        | [] -> acc
        | h :: t -> aux t (h :: acc) in
      aux list [] in

    let rec mapi f list =
      let rec aux i list =
        match list with
        | [] -> []
        | h :: t -> f i h :: aux (i + 1) t
      in aux 0 list in

    let rec append a b =
      match a with
      | [] -> b
      | h :: t -> h :: append t b in

    let collect f xs =
      let rec loop xs acc =
        match xs with
        | [] -> rev acc
        | h :: t ->
          let mapped = f h in
          loop t (append (rev mapped) acc) in
      loop xs [] in

    let rec sublist start len list =
      if len <= 0 then []
      else
        match list with
        | [] -> []
        | h :: t ->
          if start > 0 then sublist (start - 1) len t
          else h :: sublist 0 (len - 1) t in

    let rec forall p list =
      match list with
      | [] -> true
      | h :: t -> p h && forall p t in

    let notIn v xs = forall (fun x -> x <> v) xs in

    let rec access i list =
      match list with
      | h :: t -> if i = 0 then h else access (i - 1) t in

    let size = 9 in
    let box = 3 in

    let row i bd = access i bd in
    let col j bd = map (fun row -> access j row) bd in
    let cell i j bd = access j (row i bd) in

    let boxCells i j bd =
      let bi = (i / box) * box in
      let bj = (j / box) * box in
      collect (fun row -> sublist bj box row) (sublist bi box bd) in

    let ok i j v bd =
      notIn v (row i bd)
      && notIn v (col j bd)
      && notIn v (boxCells i j bd) in

    let setCell i j v bd =
      let fc = fun c x -> if c = j then v else x in
      let fr = fun r row -> if r = i then mapi fc row else row in
      mapi fr bd in

    let rec findEmpty i j bd =
      if i = size then None
      elif j = size then findEmpty (i + 1) 0 bd
      elif cell i j bd = 0 then Some (i, j)
      else findEmpty i (j + 1) bd in

    let rec solve bd =
      match findEmpty 0 0 bd with
      | None -> Some bd
      | Some (i, j) ->
        let rec tryVals v =
          if v > 9 then None
          elif ok i j v bd then
            match solve (setCell i j v bd) with
            | Some sol -> Some sol
            | None -> tryVals (v + 1)
          else tryVals (v + 1) in
        tryVals 1 in

    let puzzle = [
      [5; 7; 8;   2; 3; 0;   0; 0; 9];
      [4; 3; 0;   0; 1; 9;   0; 7; 5];
      [9; 0; 6;   0; 0; 5;   0; 0; 4];

      [0; 5; 9;   7; 8; 1;   0; 0; 2];
      [2; 0; 0;   0; 5; 6;   7; 0; 1];
      [1; 8; 7;   3; 0; 2;   9; 0; 6];

      [7; 0; 0;   0; 2; 3;   0; 9; 0];
      [3; 0; 0;   0; 0; 8;   5; 0; 7];
      [8; 9; 1;   5; 6; 7;   4; 2; 0]] in

    solve puzzle
  """
  test(
    eval(expr20),
    "(Some [" +
    "[5; 7; 8; 2; 3; 4; 6; 1; 9]; " +
    "[4; 3; 2; 6; 1; 9; 8; 7; 5]; " +
    "[9; 1; 6; 8; 7; 5; 2; 3; 4]; " +
    "[6; 5; 9; 7; 8; 1; 3; 4; 2]; " +
    "[2; 4; 3; 9; 5; 6; 7; 8; 1]; " +
    "[1; 8; 7; 3; 4; 2; 9; 5; 6]; " +
    "[7; 6; 5; 4; 2; 3; 1; 9; 8]; " +
    "[3; 2; 4; 1; 9; 8; 5; 6; 7]; " +
    "[8; 9; 1; 5; 6; 7; 4; 2; 3]" +
    "])",
    weight = 5,
  )

  // -------------------------------------------------------------------------
  // Problem #2: hanoiMoves
  // -------------------------------------------------------------------------
  def afterAllPass(doit: => String): String =
    if (passAll) doit else error("Not all interpreter tests passed yet")

  def hanoiMovesExpr(n: Int, source: Int, temp: Int, target: Int): String = s"""
    let hanoiMoves n source temp target = $hanoiMovesBody in
    hanoiMoves $n $source $temp $target
  """
  test(
    afterAllPass(eval(hanoiMovesExpr(3, 0, 1, 2))),
    "[(0, 2); (0, 1); (2, 1); (0, 2); (1, 0); (1, 2); (0, 2)]",
    weight = 50,
  )

  /* Write your own tests */
}
