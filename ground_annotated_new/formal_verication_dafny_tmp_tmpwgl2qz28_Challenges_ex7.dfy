method Exchanger(s: seq<Bases>, x: nat, y: nat)
    returns (t: seq<Bases>)
  // pre-conditions-start
  requires 0 < |s| && x < |s| && y < |s|
  // pre-conditions-end
  // post-conditions-start
  ensures |t| == |s|
  ensures forall b: nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
  ensures t[x] == s[y] && s[x] == t[y]
  ensures multiset(s) == multiset(t)
  // post-conditions-end
{
// impl-start
  t := s;
  t := t[x := s[y]];
  t := t[y := s[x]];
  return t;
// impl-end
}

function below(first: Bases, second: Bases): bool
{
  first == second || first == A || (first == C && (second == G || second == T)) || (first == G && second == T) || second == T
}
// pure-end

function bordered(s: seq<Bases>): bool
{
  forall j, k :: 
    0 <= j < k < |s| ==>
      below(s[j], s[k])
}
// pure-end

method Sorter(bases: seq<Bases>) returns (sobases: seq<Bases>)
  // pre-conditions-start
  requires 0 < |bases|
  // pre-conditions-end
  // post-conditions-start
  ensures |sobases| == |bases|
  ensures bordered(sobases)
  ensures multiset(bases) == multiset(sobases)
  // post-conditions-end
{
// impl-start
  sobases := bases;
  var c, next: nat := 0, 0;
  var g, t: nat := |bases|, |bases|;
  while next != g
    // invariants-start

    invariant 0 <= c <= next <= g <= t <= |bases|
    invariant |sobases| == |bases|
    invariant multiset(bases) == multiset(sobases)
    invariant forall i: nat :: 0 <= i < c ==> sobases[i] == A
    invariant forall i: nat :: c <= i < next ==> sobases[i] == C
    invariant forall i: nat :: g <= i < t ==> sobases[i] == G
    invariant forall i: nat :: t <= i < |bases| ==> sobases[i] == T
    // invariants-end

  {
    match sobases[next] {
      case {:split false} C =>
        next := next + 1;
      case {:split false} A =>
        sobases := Exchanger(sobases, next, c);
        c, next := c + 1, next + 1;
      case {:split false} G =>
        g := g - 1;
        sobases := Exchanger(sobases, next, g);
      case {:split false} T =>
        g, t := g - 1, t - 1;
        sobases := Exchanger(sobases, next, t);
        if g != t {
          sobases := Exchanger(sobases, next, g);
        }
    }
  }
  return sobases;
// impl-end
}

method Testerexchange()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: seq<Bases> := [A, C, A, T];
  var b: seq<Bases> := Exchanger(a, 2, 3);
  // assert-start
  assert b == [A, C, T, A];
  // assert-end

  var c: seq<Bases> := [A, C, A, T, A, T, C];
  var d: seq<Bases> := Exchanger(c, 5, 1);
  // assert-start
  assert d == [A, T, A, T, A, C, C];
  // assert-end

  var e: seq<Bases> := [A, C, A, T, A, T, C];
  var f: seq<Bases> := Exchanger(e, 1, 1);
  // assert-start
  assert f == [A, C, A, T, A, T, C];
  // assert-end

  var g: seq<Bases> := [A, C];
  var h: seq<Bases> := Exchanger(g, 0, 1);
  // assert-start
  assert h == [C, A];
  // assert-end

// impl-end
}

method Testsort()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: seq<Bases> := [G, A, T];
  // assert-start
  assert a == [G, A, T];
  // assert-end

  var b: seq<Bases> := Sorter(a);
  // assert-start
  assert bordered(b);
  // assert-end

  // assert-start
  assert multiset(b) == multiset(a);
  // assert-end

  var c: seq<Bases> := [G, A, T, T, A, C, G, C, T, A, C, G, T, T, G];
  // assert-start
  assert c == [G, A, T, T, A, C, G, C, T, A, C, G, T, T, G];
  // assert-end

  var d: seq<Bases> := Sorter(c);
  // assert-start
  assert bordered(d);
  // assert-end

  // assert-start
  assert multiset(c) == multiset(d);
  // assert-end

  var e: seq<Bases> := [A];
  // assert-start
  assert e == [A];
  // assert-end

  var f: seq<Bases> := Sorter(e);
  // assert-start
  assert bordered(b);
  // assert-end

  // assert-start
  assert multiset(e) == multiset(f);
  // assert-end

  var g: seq<Bases> := [A, C, G, T];
  // assert-start
  assert g == [A, C, G, T];
  // assert-end

  var h: seq<Bases> := Sorter(g);
  // assert-start
  assert bordered(b);
  // assert-end

  // assert-start
  assert multiset(g) == multiset(h);
  // assert-end

  var i: seq<Bases> := [A, T, C, T, T];
  // assert-start
  assert i[0] == A && i[1] == T && i[2] == C && i[3] == T && i[4] == T;
  // assert-end

  // assert-start
  assert !bordered(i);
  // assert-end

// impl-end
}

datatype Bases = A | C | G | T
