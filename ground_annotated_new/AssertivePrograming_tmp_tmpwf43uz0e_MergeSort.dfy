function Sorted(q: seq<int>): bool
{
  forall i, j :: 
    0 <= i <= j < |q| ==>
      q[i] <= q[j]
}
// pure-end

method MergeSort(a: array<int>) returns (b: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
  decreases a.Length
  // post-conditions-end
{
// impl-start
  if a.Length <= 1 {
    b := a;
  } else {
    var mid: nat := a.Length / 2;
    var a1: array<int> := new int[mid];
    var a2: array<int> := new int[a.Length - mid];
    // assert-start
    assert a1.Length <= a2.Length;
    // assert-end

    // assert-start
    assert a.Length == a1.Length + a2.Length;
    // assert-end

    var i: nat := 0;
    while i < a1.Length
      // invariants-start

      invariant Inv(a[..], a1[..], a2[..], i, mid)
      decreases a1.Length - i
      // invariants-end

    {
      a1[i] := a[i];
      a2[i] := a[i + mid];
      i := i + 1;
    }
    // assert-start
    assert !(i < a1.Length);
    // assert-end

    // assert-start
    assert i >= a1.Length;
    // assert-end

    // assert-start
    assert i == a1.Length;
    // assert-end

    // assert-start
    assert Inv(a[..], a1[..], a2[..], i, mid);
    // assert-end

    // assert-start
    assert i <= |a1[..]| && i <= |a2[..]| && i + mid <= |a[..]|;
    // assert-end

    // assert-start
    assert a1[..i] == a[..i] && a2[..i] == a[mid .. i + mid];
    // assert-end

    if a1.Length < a2.Length {
      a2[i] := a[i + mid];
      // assert-start
      assert i + 1 == a2.Length;
      // assert-end

      // assert-start
      assert a2[..i + 1] == a[mid .. i + 1 + mid];
      // assert-end

      // assert-start
      assert a1[..i] == a[..i] && a2[..i + 1] == a[mid .. i + 1 + mid];
      // assert-end

      // assert-start
      assert a[..i] + a[i .. i + 1 + mid] == a1[..i] + a2[..i + 1];
      // assert-end

      // assert-start
      assert a[..i] + a[i .. i + 1 + mid] == a1[..] + a2[..];
      // assert-end

      // assert-start
      assert a[..] == a1[..] + a2[..];
      // assert-end

    } else {
      // assert-start
      assert i == a2.Length;
      // assert-end

      // assert-start
      assert a1[..i] == a[..i] && a2[..i] == a[mid .. i + mid];
      // assert-end

      // assert-start
      assert a[..i] + a[i .. i + mid] == a1[..i] + a2[..i];
      // assert-end

      // assert-start
      assert a[..i] + a[i .. i + mid] == a1[..] + a2[..];
      // assert-end

      // assert-start
      assert a[..] == a1[..] + a2[..];
      // assert-end

    }
    // assert-start
    assert a1.Length < a.Length;
    // assert-end

    a1 := MergeSort(a1);
    // assert-start
    assert a2.Length < a.Length;
    // assert-end

    a2 := MergeSort(a2);
    b := new int[a.Length];
    Merge(b, a1, a2);
    // assert-start
    assert multiset(b[..]) == multiset(a1[..]) + multiset(a2[..]);
    // assert-end

    // assert-start
    assert Sorted(b[..]);
    // assert-end

  }
  // assert-start
  assert b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..]);
  // assert-end

// impl-end
}

function Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat): bool
{
  i <= |a1| &&
  i <= |a2| &&
  i + mid <= |a| &&
  a1[..i] == a[..i] &&
  a2[..i] == a[mid .. i + mid]
}
// pure-end

method Merge(b: array<int>, c: array<int>, d: array<int>)
  // pre-conditions-start
  requires b != c && b != d && b.Length == c.Length + d.Length
  requires Sorted(c[..]) && Sorted(d[..])
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..]) + multiset(d[..])
  // post-conditions-end
{
// impl-start
  var i: nat, j: nat := 0, 0;
  while i + j < b.Length
    // invariants-start

    invariant i <= c.Length && j <= d.Length && i + j <= b.Length
    invariant InvSubSet(b[..], c[..], d[..], i, j)
    invariant InvSorted(b[..], c[..], d[..], i, j)
    decreases c.Length - i, d.Length - j
    // invariants-end

  {
    i, j := MergeLoop(b, c, d, i, j);
    // assert-start
    assert InvSubSet(b[..], c[..], d[..], i, j);
    // assert-end

    // assert-start
    assert InvSorted(b[..], c[..], d[..], i, j);
    // assert-end

  }
  // assert-start
  assert InvSubSet(b[..], c[..], d[..], i, j);
  // assert-end

  // assert-start
  LemmaMultysetsEquals(b[..], c[..], d[..], i, j);
  // assert-end

  // assert-start
  assert multiset(b[..]) == multiset(c[..]) + multiset(d[..]);
  // assert-end

// impl-end
}

method {:verify true} MergeLoop(b: array<int>, c: array<int>, d: array<int>, i0: nat, j0: nat)
    returns (i: nat, j: nat)
  // pre-conditions-start
  requires b != c && b != d && b.Length == c.Length + d.Length
  requires Sorted(c[..]) && Sorted(d[..])
  requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
  requires InvSubSet(b[..], c[..], d[..], i0, j0)
  requires InvSorted(b[..], c[..], d[..], i0, j0)
  requires i0 + j0 < b.Length
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures i <= c.Length && j <= d.Length && i + j <= b.Length
  ensures InvSubSet(b[..], c[..], d[..], i, j)
  ensures InvSorted(b[..], c[..], d[..], i, j)
  ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
  // post-conditions-end
{
// impl-start
  i, j := i0, j0;
  if i == c.Length || (j < d.Length && d[j] < c[i]) {
    // assert-start
    assert InvSorted(b[..][i + j := d[j]], c[..], d[..], i, j + 1);
    // assert-end

    b[i + j] := d[j];
    // assert-start
    lemmaInvSubsetTakeValueFromD(b[..], c[..], d[..], i, j);
    // assert-end

    // assert-start
    assert InvSubSet(b[..], c[..], d[..], i, j + 1);
    // assert-end

    // assert-start
    assert InvSorted(b[..], c[..], d[..], i, j + 1);
    // assert-end

    j := j + 1;
  } else {
    // assert-start
    assert j == d.Length || (i < c.Length && c[i] <= d[j]);
    // assert-end

    // assert-start
    assert InvSorted(b[..][i + j := c[i]], c[..], d[..], i + 1, j);
    // assert-end

    b[i + j] := c[i];
    // assert-start
    lemmaInvSubsetTakeValueFromC(b[..], c[..], d[..], i, j);
    // assert-end

    // assert-start
    assert InvSubSet(b[..], c[..], d[..], i + 1, j);
    // assert-end

    // assert-start
    assert InvSorted(b[..], c[..], d[..], i + 1, j);
    // assert-end

    i := i + 1;
  }
// impl-end
}

function InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat): bool
{
  i <= |c| &&
  j <= |d| &&
  i + j <= |b| &&
  (i + j > 0 &&
  i < |c| ==>
    b[j + i - 1] <= c[i]) &&
  (i + j > 0 &&
  j < |d| ==>
    b[j + i - 1] <= d[j]) &&
  Sorted(b[..i + j])
}
// pure-end

function InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat): bool
{
  i <= |c| &&
  j <= |d| &&
  i + j <= |b| &&
  multiset(b[..i + j]) == multiset(c[..i]) + multiset(d[..j])
}
// pure-end

lemma LemmaMultysetsEquals(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
  // pre-conditions-start
  requires i == |c|
  requires j == |d|
  requires i + j == |b|
  requires multiset(b[..i + j]) == multiset(c[..i]) + multiset(d[..j])
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(b[..]) == multiset(c[..]) + multiset(d[..])
  // post-conditions-end
{
// impl-start
  assert b[..] == b[..i + j];
  assert c[..] == c[..i];
  assert d[..] == d[..j];
// impl-end
}

lemma lemmaInvSubsetTakeValueFromC(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
  // pre-conditions-start
  requires i < |c|
  requires j <= |d|
  requires i + j < |b|
  requires |c| + |d| == |b|
  requires multiset(b[..i + j]) == multiset(c[..i]) + multiset(d[..j])
  requires b[i + j] == c[i]
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(b[..i + j + 1]) == multiset(c[..i + 1]) + multiset(d[..j])
  // post-conditions-end
{
// impl-start
  assert c[..i] + [c[i]] == c[..i + 1];
  assert b[..i + j + 1] == b[..i + j] + [b[i + j]];
  assert multiset(b[..i + j + 1]) == multiset(c[..i + 1]) + multiset(d[..j]);
// impl-end
}

lemma {:verify true} lemmaInvSubsetTakeValueFromD(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
  // pre-conditions-start
  requires i <= |c|
  requires j < |d|
  requires i + j < |b|
  requires |c| + |d| == |b|
  requires multiset(b[..i + j]) == multiset(c[..i]) + multiset(d[..j])
  requires b[i + j] == d[j]
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(b[..i + j + 1]) == multiset(c[..i]) + multiset(d[..j + 1])
  // post-conditions-end
{
// impl-start
  assert d[..j] + [d[j]] == d[..j + 1];
  assert b[..i + j + 1] == b[..i + j] + [b[i + j]];
  assert multiset(b[..i + j + 1]) == multiset(c[..i]) + multiset(d[..j + 1]);
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[3] [4, 8, 6];
  var q0 := a[..];
  // assert-start
  assert q0 == [4, 8, 6];
  // assert-end

  a := MergeSort(a);
  // assert-start
  assert a.Length == |q0| && multiset(a[..]) == multiset(q0);
  // assert-end

  print "\nThe sorted version of ", q0, " is ", a[..];
  // assert-start
  assert Sorted(a[..]);
  // assert-end

  // assert-start
  assert a[..] == [4, 6, 8];
  // assert-end

  a := new int[5] [3, 8, 5, -1, 10];
  q0 := a[..];
  // assert-start
  assert q0 == [3, 8, 5, -1, 10];
  // assert-end

  a := MergeSort(a);
  // assert-start
  assert a.Length == |q0| && multiset(a[..]) == multiset(q0);
  // assert-end

  print "\nThe sorted version of ", q0, " is ", a[..];
  // assert-start
  assert Sorted(a[..]);
  // assert-end

// impl-end
}
