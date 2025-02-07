function SumR(s: seq<int>): int
  decreases s
{
  if s == [] then
    0
  else
    SumR(s[..|s| - 1]) + s[|s| - 1]
}
// pure-end

function SumL(s: seq<int>): int
  decreases s
{
  if s == [] then
    0
  else
    s[0] + SumL(s[1..])
}
// pure-end

lemma concatLast(s: seq<int>, t: seq<int>)
  // pre-conditions-start
  requires t != []
  // pre-conditions-end
  // post-conditions-start
  ensures (s + t)[..|s + t| - 1] == s + t[..|t| - 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma concatFirst(s: seq<int>, t: seq<int>)
  // pre-conditions-start
  requires s != []
  // pre-conditions-end
  // post-conditions-start
  ensures (s + t)[1..] == s[1..] + t
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma {:induction s, t} SumByPartsR(s: seq<int>, t: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SumR(s + t) == SumR(s) + SumR(t)
  decreases s, t
  // post-conditions-end
{
// impl-start
  if t == [] {
    assert s + t == s;
  } else if s == [] {
    assert s + t == t;
  } else {
    calc == {
      SumR(s + t);
      SumR((s + t)[..|s + t| - 1]) + (s + t)[|s + t| - 1];
      SumR((s + t)[..|s + t| - 1]) + t[|t| - 1];
      {
        concatLast(s, t);
      }
      SumR(s + t[..|t| - 1]) + t[|t| - 1];
      {
        SumByPartsR(s, t[..|t| - 1]);
      }
      SumR(s) + SumR(t[..|t| - 1]) + t[|t| - 1];
      SumR(s) + SumR(t);
    }
  }
// impl-end
}

lemma {:induction s, t} SumByPartsL(s: seq<int>, t: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SumL(s + t) == SumL(s) + SumL(t)
  decreases s, t
  // post-conditions-end
{
// impl-start
  if t == [] {
    assert s + t == s;
  } else if s == [] {
    assert s + t == t;
  } else {
    calc == {
      SumL(s + t);
      (s + t)[0] + SumL((s + t)[1..]);
      s[0] + SumL((s + t)[1..]);
      {
        concatFirst(s, t);
      }
      s[0] + SumL(s[1..] + t);
      {
        SumByPartsL(s[1..], t);
      }
      s[0] + SumL(s[1..]) + SumL(t);
    }
  }
// impl-end
}

lemma {:induction s, i, j} equalSumR(s: seq<int>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i <= j <= |s|
  // pre-conditions-end
  // post-conditions-start
  ensures SumR(s[i .. j]) == SumL(s[i .. j])
  decreases j - i
  // post-conditions-end
{
// impl-start
  if s == [] {
    assert SumR(s) == SumL(s);
  } else {
    if i == j {
      assert SumR(s[i .. j]) == SumL(s[i .. j]);
    } else {
      calc == {
        SumR(s[i .. j]);
        {
          assert s[i .. j] == s[i .. j - 1] + [s[j - 1]];
          assert SumR(s[i .. j]) == SumR(s[i .. j - 1]) + s[j - 1];
        }
        SumR(s[i .. j - 1]) + s[j - 1];
        {
          equalSumR(s, i, j - 1);
        }
        SumL(s[i .. j - 1]) + s[j - 1];
        {
          assert s[j - 1] == SumL([s[j - 1]]);
        }
        SumL(s[i .. j - 1]) + SumL([s[j - 1]]);
        {
          SumByPartsL(s[i .. j - 1], [s[j - 1]]);
        }
        SumL(s[i .. j - 1] + [s[j - 1]]);
        {
          assert s[i .. j] == s[i .. j - 1] + [s[j - 1]];
        }
        SumL(s[i .. j]);
      }
    }
  }
// impl-end
}

lemma equalSumsV()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall v: array<int>, i, j | 0 <= i <= j <= v.Length :: SumR(v[i .. j]) == SumL(v[i .. j])
  // post-conditions-end
{
// impl-start
  forall v: array<int>, i, j | 0 <= i <= j <= v.Length
    ensures SumR(v[i .. j]) == SumL(v[i .. j])
  {
    equalSumR(v[..], i, j);
  }
// impl-end
}

function SumV(v: array<int>, c: int, f: int): int
  requires 0 <= c <= f <= v.Length
  reads v
{
  SumR(v[c .. f])
}
// pure-end

lemma ArrayFacts<T>()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall v: array<T> :: v[..v.Length] == v[..]
  ensures forall v: array<T> :: v[0..] == v[..]
  ensures forall v: array<T> :: v[0 .. v.Length] == v[..]
  ensures forall v: array<T> :: |v[0 .. v.Length]| == v.Length
  ensures forall v: array<T> | v.Length >= 1 :: |v[1 .. v.Length]| == v.Length - 1
  ensures forall v: array<T> :: forall k: nat | k < v.Length :: v[..k + 1][..k] == v[..k]
  // post-conditions-end
{
// impl-start
  equalSumsV();
// impl-end
}

method sumElems(v: array<int>) returns (sum: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sum == SumR(v[..])
  // post-conditions-end
{
// impl-start
  // assert-start
  ArrayFacts<int>();
  // assert-end

  sum := 0;
  var i: int;
  i := 0;
  while i < v.Length
    // invariants-start

    invariant 0 <= i <= v.Length && sum == SumR(v[..i])
    decreases v.Length - i
    // invariants-end

  {
    sum := sum + v[i];
    i := i + 1;
  }
// impl-end
}

method sumElemsB(v: array<int>) returns (sum: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sum == SumR(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  // assert-start
  ArrayFacts<int>();
  // assert-end

  sum := 0;
  var i: int;
  i := v.Length;
  // assert-start
  equalSumsV();
  // assert-end

  while i > 0
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant sum == SumL(v[i..]) == SumR(v[i..])
    decreases i
    // invariants-end

  {
    sum := sum + v[i - 1];
    i := i - 1;
  }
// impl-end
}
