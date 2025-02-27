// dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_PrecedenceLinter.dfy

predicate P0(A: bool, B: bool, C: bool)
{
  A &&
  B ==>
    C
}
// pure-end

predicate P1(A: bool, B: bool, C: bool)
{
  A &&
  B ==>
    C
}
// pure-end

predicate P2(A: bool, B: bool, C: bool)
{
  A &&
  B ==>
    C
}
// pure-end

predicate P3(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate P4(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate P5(A: bool, B: bool, C: bool)
{
  A ==>
    B &&
    C
}
// pure-end

predicate P6(A: bool, B: bool, C: bool)
{
  A ==>
    B || C
}
// pure-end

predicate Q0(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q1(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q2(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q3(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q4(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q4a(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q4b(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q4c(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q4d(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q5(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q6(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    C &&
    D
}
// pure-end

predicate Q7(A: bool, B: bool, C: bool, D: bool)
{
  A ==>
    B &&
    C &&
    D
}
// pure-end

predicate Q8(A: bool, B: bool, C: bool, D: bool)
{
  A ==>
    B &&
    C &&
    D
}
// pure-end

predicate Q8a(A: bool, B: bool, C: bool, D: bool)
{
  (A ==>
    B &&
    C &&
    D) &&
  (B || C)
}
// pure-end

predicate Q8b(A: bool, B: bool, C: bool, D: bool)
{
  A &&
  B ==>
    B &&
    D
}
// pure-end

predicate Q8c(t: int, x: int, y: int)
{
  (t == 2 ==>
    x < y) &&
  (t == 3 || t == 2 ==>
    x == 100 &&
    y == 1000) &&
  (t == 4 ==>
    0 <= x || 0 <= y)
}
// pure-end

predicate Q8d(t: int, x: int, y: int)
{
  t == 3 || t == 2 ==>
    x == 100 &&
    y == 1000
}
// pure-end

predicate Q9(A: bool, B: bool, C: bool)
{
  A ==>
    B ==>
      C
}
// pure-end

ghost predicate R0(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) &&
      R(x)
}
// pure-end

ghost predicate R1(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) &&
    Q(x) ==>
      R(x)
}
// pure-end

ghost predicate R2(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}
// pure-end

ghost predicate R3(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}
// pure-end

ghost predicate R4(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      Q(x) ==>
        R(x)
}
// pure-end

ghost predicate R5(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==>
      forall y :: 
        Q(y) ==>
          R(x)
}
// pure-end

ghost predicate R6(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}
// pure-end

ghost predicate R7(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}
// pure-end

ghost predicate R8(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}
// pure-end

ghost predicate R9(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  exists x :: 
    (P(x) ==>
      Q(x)) &&
    R(x)
}
// pure-end

ghost predicate R10(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  exists x :: 
    P(x) &&
    exists y :: 
      Q(y) &&
      R(x)
}
// pure-end

lemma Injective()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x, y :: Negate(x) == Negate(y) ==> x == y
  // post-conditions-end
{
// impl-start
// impl-end
}

function Negate(x: int): int
{
  -x
}
// pure-end

predicate Quant0(s: string)
{
  s != [] &&
  ('a' <= s[0] <= 'z' || 'A' <= s[0] <= 'Z') &&
  forall i :: 
    1 <= i < |s| ==>
      'a' <= s[i] <= 'z' || 'A' <= s[i] <= 'Z' || '0' <= s[i] <= '9'
}
// pure-end

predicate Quant1(m: array2<string>, P: int -> bool)
  reads m
{
  forall i :: 
    0 <= i < m.Length0 &&
    P(i) ==>
      forall j :: 
        0 <= j < m.Length1 ==>
          m[i, j] != ""
}
// pure-end

predicate Quant2(s: string)
{
  forall i :: 
    0 <= i < |s| ==>
      if s[i] == '*' then false else s[i] == 'a' || s[i] == 'b'
}
// pure-end

ghost predicate Quant3(f: int -> int, g: int -> int)
{
  forall x :: 
    f(x) == g(x)
}
// pure-end

ghost predicate Quant4(f: int -> int, g: int -> int)
{
  forall x :: 
    f(x) == g(x)
}
// pure-end

ghost predicate Quant5(f: int -> int, g: int -> int)
{
  forall x :: 
    f(x) == g(x)
}
// pure-end

function If0(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}
// pure-end

function If1(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}
// pure-end

function If2(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}
// pure-end

function If3(s: string): int
{
  if |s| == 3 then
    2
  else
    3 + 2 * |s|
}
// pure-end

predicate Waterfall(A: bool, B: bool, C: bool, D: bool, E: bool)
{
  A ==>
    B ==>
      C ==>
        D ==>
          E
}
// pure-end

ghost predicate MoreOps0(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) <==
      Q(x) <==
      R(x)
}
// pure-end

ghost predicate MoreOps1(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) <== Q(x) <==> R(x)
}
// pure-end

ghost predicate MoreOps2(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==> Q(x) <==> R(x)
}
// pure-end

ghost predicate MoreOps3(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) ==> Q(x) <==> R(x) ==> P(x)
}
// pure-end

ghost predicate MoreOps4(P: int -> bool, Q: int -> bool, R: int -> bool)
{
  forall x :: 
    P(x) <==> Q(x) && R(x)
}
// pure-end

lemma IntLemma(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end

function StmtExpr0(x: int): int
{
  if x == 17 then
    2
  else
    IntLemma(x); 3
}
// pure-end

function StmtExpr1(x: int): int
{
  if x == 17 then
    2
  else
    IntLemma(x); 3
}
// pure-end

function StmtExpr2(x: int): int
{
  if x == 17 then
    2
  else
    assert x != 17; 3
}
// pure-end

function StmtExpr3(x: int): int
{
  if x == 17 then
    2
  else
    assert x != 17; 3
}
// pure-end

function FunctionWithDefaultParameterValue(x: int, y: int := 100): int
// pure-end

function UseDefaultValues(x: int): int
{
  if x <= 0 then
    0
  else
    FunctionWithDefaultParameterValue(x - 1)
}
// pure-end

function Square(x: int): int
{
  x * x
}
// pure-end

predicate Let0(lo: int, hi: int)
  requires lo <= hi
{
  forall x :: 
    lo <= x < hi ==>
      var square := Square(x); 0 <= square
}
// pure-end

ghost predicate Let1(P: int -> bool)
{
  forall x :: 
    0 <= x &&
    P(x) ==>
      var bigger :| x <= bigger; 0 <= bigger
}
// pure-end

predicate SomeProperty<X>(x: X)
// pure-end

method Parentheses0(arr: array<int>, P: int -> bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i]);
  // assert-end

  var x := forall i :: 0 <= i < arr.Length ==> SomeProperty(arr[i]);
  var y := forall i :: 0 <= i < arr.Length ==> P(arr[i]);
  // assert-start
  assert forall i :: 0 <= i < arr.Length && SomeProperty(i) ==> unchanged(arr);
  // assert-end

  var u := if arr.Length == 3 then true else fresh(arr);
// impl-end
}

method Parentheses1(w: bool, x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := if w then {} else {x, x, x};
  var b := if w then iset{} else iset{x, x, x};
  var c := if w then [] else [x, x, x];
  var d := if w then multiset{} else multiset{x, x, x};
  var e := if w then map[] else map[x := x];
  var f := if w then imap[] else imap[x := x];
// impl-end
}

method Parentheses2(w: bool, x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := if w then Record(0, 0) else Record(x, y);
  var b := if w then a else a.(x := y);
// impl-end
}

method Parentheses3(w: bool, arr: array<int>, m: array2<int>, i: nat, j: nat)
  // pre-conditions-start
  requires i < j < arr.Length <= m.Length0 <= m.Length1
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := if w then 0 else arr[i];
  var b := if w then [] else arr[i..];
  var c := if w then [] else arr[..i];
  var d := if w then [] else arr[i .. j];
  var e := if w then [] else arr[..j][i..];
  var f := if w then [] else arr[..i] + arr[i..];
  var g := if w then 0 else m[i, j];
  var h := if w then arr[..] else arr[..j][0 := 25];
// impl-end
}

method Parentheses4(w: bool, s: Stream, t: Stream)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  ghost var a := if w then true else s ==#[12] t;
  ghost var b := if w then true else s ==#[12] t;
  ghost var c := if w then true else s !=#[12] t;
  ghost var d := if w then true else s !=#[12] t;
// impl-end
}

datatype Record = Record(x: int, y: int)

codatatype Stream = More(head: int, tail: Stream)

module MyModule {
  function MyFunction(x: int): int
  // pure-end

  lemma Lemma(x: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
}

module QualifiedNames {
  predicate P(x: int)
  {
    var u := x;
    MyModule.MyFunction(x) == x
  }
  // pure-end

  predicate Q(x: int)
  {
    var u := x;
    MyModule.Lemma(x);
    x == MyModule.MyFunction(x)
  }
  // pure-end

  function F(): int
  {
    var p := 1000;
    MyModule.Lemma(p);
    p
  }
  // pure-end

  predicate R(x: int)
  {
    var u := x;
    MyModule.Lemma(x);
    x == MyModule.MyFunction(x)
  }
  // pure-end

  import MyModule
}

module MatchAcrossMultipleLines {
  method M(s: set<PQ>)
    // pre-conditions-start
    requires forall pq | pq in s :: match pq { case P(x) => true case Q(y) => y == false }
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  function F(A: bool, B: int, C: YZ): int
    requires C != Y
  {
    if A then
      B
    else
      match C { case Z => 3 }
  }
  // pure-end

  datatype PQ = P(int) | Q(bool)

  datatype YZ = Y | Z
}
