function Count(hi: nat, s: seq<int>): int
  requires 0 <= hi <= |s|
  decreases hi
{
  if hi == 0 then
    0
  else if s[hi - 1] % 2 == 0 then
    1 + Count(hi - 1, s)
  else
    Count(hi - 1, s)
}
// pure-end

method FooCount(CountIndex: nat, a: seq<int>, b: array<int>)
    returns (p: nat)
  // pre-conditions-start
  requires CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures p == Count(CountIndex, a)
  decreases CountIndex
  // post-conditions-end
{
// impl-start
  // assert-start
  assert CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|);
  // assert-end

  // assert-start
  assert CountIndex == 0 || (|a| == b.Length && 0 <= CountIndex - 1 <= |a|);
  // assert-end

  // assert-start
  assert CountIndex != 0 ==> |a| == b.Length && 0 <= CountIndex - 1 <= |a|;
  // assert-end

  // assert-start
  assert CountIndex == 0 ==> true && CountIndex != 0 ==> |a| == b.Length && 0 <= CountIndex - 1 <= |a|;
  // assert-end

  if CountIndex == 0 {
    // assert-start
    assert true;
    // assert-end

    // assert-start
    assert 0 == 0;
    // assert-end

    // assert-start
    assert 0 == Count(0, a);
    // assert-end

    p := 0;
    // assert-start
    assert p == Count(CountIndex, a);
    // assert-end

  } else {
    // assert-start
    assert |a| == b.Length && 0 <= CountIndex - 1 <= |a|;
    // assert-end

    // assert-start
    assert (a[CountIndex - 1] % 2 == 0 ==> |a| == b.Length && 0 <= CountIndex - 1 < |a| && 1 + Count(CountIndex - 1, a) == Count(CountIndex, a)) && (a[CountIndex - 1] % 2 != 0 ==> |a| == b.Length && 0 <= CountIndex - 1 < |a| && Count(CountIndex - 1, a) == Count(CountIndex, a));
    // assert-end

    if a[CountIndex - 1] % 2 == 0 {
      // assert-start
      assert |a| == b.Length && 0 <= CountIndex - 1 < |a| && 1 + Count(CountIndex - 1, a) == Count(CountIndex, a);
      // assert-end

      var d := FooCount(CountIndex - 1, a, b);
      // assert-start
      assert d + 1 == Count(CountIndex, a);
      // assert-end

      p := d + 1;
      // assert-start
      assert p == Count(CountIndex, a);
      // assert-end

    } else {
      // assert-start
      assert |a| == b.Length && 0 <= CountIndex - 1 < |a| && Count(CountIndex - 1, a) == Count(CountIndex, a);
      // assert-end

      // assert-start
      assert |a| == b.Length && 0 <= CountIndex - 1 < |a| && forall p' :: p' == Count(CountIndex - 1, a) ==> p' == Count(CountIndex, a);
      // assert-end

      var d := FooCount(CountIndex - 1, a, b);
      // assert-start
      assert d == Count(CountIndex, a);
      // assert-end

      p := d;
      // assert-start
      assert p == Count(CountIndex, a);
      // assert-end

    }
    b[CountIndex - 1] := p;
    // assert-start
    assert p == Count(CountIndex, a);
    // assert-end

  }
// impl-end
}

method FooPreCompute(a: array<int>, b: array<int>)
  // pre-conditions-start
  requires a.Length == b.Length
  // pre-conditions-end
  // post-conditions-start
  modifies b
  // post-conditions-end
{
// impl-start
  var CountIndex := 1;
  while CountIndex != a.Length + 1
    // invariants-start

    invariant 1 <= CountIndex <= a.Length + 1
    decreases a.Length + 1 - CountIndex
    // invariants-end

  {
    // assert-start
    assert (CountIndex == 0 || (a.Length == b.Length && 1 <= CountIndex <= a.Length)) && forall a' :: a' == Count(CountIndex, a[..]) ==> a' == Count(CountIndex, a[..]);
    // assert-end

    var p := FooCount(CountIndex, a[..], b);
    // assert-start
    assert 1 <= CountIndex <= a.Length;
    // assert-end

    // assert-start
    assert 1 <= CountIndex + 1 <= a.Length + 1;
    // assert-end

    CountIndex := CountIndex + 1;
    // assert-start
    assert 1 <= CountIndex <= a.Length + 1;
    // assert-end

  }
// impl-end
}

method ComputeCount(CountIndex: nat, a: seq<int>, b: array<int>)
    returns (p: nat)
  // pre-conditions-start
  requires CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures p == Count(CountIndex, a)
  decreases CountIndex
  // post-conditions-end
{
// impl-start
  if CountIndex == 0 {
    p := 0;
  } else {
    if a[CountIndex - 1] % 2 == 0 {
      var d := ComputeCount(CountIndex - 1, a, b);
      p := d + 1;
    } else {
      var d := ComputeCount(CountIndex - 1, a, b);
      p := d;
    }
    b[CountIndex - 1] := p;
  }
// impl-end
}

method PreCompute(a: array<int>, b: array<int>) returns (p: nat)
  // pre-conditions-start
  requires a.Length == b.Length
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) && forall p :: p == Count(b.Length, a[..]) ==> p == Count(b.Length, a[..])
  // post-conditions-end
{
// impl-start
  // assert-start
  assert (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) && forall p :: p == Count(b.Length, a[..]) ==> p == Count(b.Length, a[..]);
  // assert-end

  p := ComputeCount(b.Length, a[..], b);
// impl-end
}

method Evens(a: array<int>) returns (c: array2<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  c := new int[a.Length, a.Length];
  var b := new int[a.Length];
  var foo := PreCompute(a, b);
  var m := 0;
  while m != a.Length
    // invariants-start

    invariant 0 <= m <= a.Length
    invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length ==> j < i ==> c[i, j] == 0
    invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length ==> j >= i ==> i > 0 ==> c[i, j] == b[j] - b[i - 1]
    invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length ==> j >= i ==> i == 0 ==> c[i, j] == b[j]
    decreases a.Length - m
    modifies c
    // invariants-end

  {
    var n := 0;
    while n != a.Length
      // invariants-start

      invariant 0 <= n <= a.Length
      invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length ==> j < i ==> c[i, j] == 0
      invariant forall j :: 0 <= j < n ==> j < m ==> c[m, j] == 0
      invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length ==> j >= i ==> i > 0 ==> c[i, j] == b[j] - b[i - 1]
      invariant forall j :: 0 <= j < n ==> j >= m ==> m > 0 ==> c[m, j] == b[j] - b[m - 1]
      invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length ==> j >= i ==> i == 0 ==> c[i, j] == b[j]
      invariant forall j :: 0 <= j < n ==> j >= m ==> m == 0 ==> c[m, j] == b[j]
      decreases a.Length - n
      modifies c
      // invariants-end

    {
      if n < m {
        c[m, n] := 0;
      } else {
        if m > 0 {
          c[m, n] := b[n] - b[m - 1];
        } else {
          c[m, n] := b[n];
        }
      }
      n := n + 1;
    }
    m := m + 1;
  }
// impl-end
}

method Mult(x: int, y: int) returns (r: int)
  // pre-conditions-start
  requires x >= 0 && y >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == x * y
  decreases x
  // post-conditions-end
{
// impl-start
  if x == 0 {
    r := 0;
  } else {
    // assert-start
    assert x - 1 >= 0 && y >= 0 && (x - 1) * y + y == x * y;
    // assert-end

    var z := Mult(x - 1, y);
    // assert-start
    assert z + y == x * y;
    // assert-end

    r := z + y;
    // assert-start
    assert r == x * y;
    // assert-end

  }
// impl-end
}
