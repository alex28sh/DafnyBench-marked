method join(a: array<int>, b: array<int>) returns (c: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a[..] + b[..] == c[..]
  ensures multiset(a[..] + b[..]) == multiset(c[..])
  ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
  ensures a.Length + b.Length == c.Length
  ensures forall i :: 0 <= i < a.Length ==> c[i] == a[i]
  ensures forall i_2, j_2 :: a.Length <= i_2 < c.Length && 0 <= j_2 < b.Length && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
  // post-conditions-end
{
// impl-start
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant c[..i] == a[..i]
    invariant multiset(c[..i]) == multiset(a[..i])
    invariant forall k :: 0 <= k < i < a.Length ==> c[k] == a[k]
    // invariants-end

  {
    c[i] := a[i];
    i := i + 1;
  }
  i := a.Length;
  var j := 0;
  while i < c.Length && j < b.Length
    // invariants-start

    invariant 0 <= j <= b.Length
    invariant 0 <= a.Length <= i <= c.Length
    invariant c[..a.Length] == a[..a.Length]
    invariant c[a.Length .. i] == b[..j]
    invariant c[..a.Length] + c[a.Length .. i] == a[..a.Length] + b[..j]
    invariant multiset(c[a.Length .. i]) == multiset(b[..j])
    invariant multiset(c[..a.Length] + c[a.Length .. i]) == multiset(a[..a.Length] + b[..j])
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall i_2, j_2 :: a.Length <= i_2 < i && 0 <= j_2 < j && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
    invariant forall k_2, i_2, j_2 :: 0 <= k_2 < a.Length && a.Length <= i_2 < i && 0 <= j_2 < j && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2] && c[k_2] == a[k_2]
    // invariants-end

  {
    c[i] := b[j];
    i := i + 1;
    j := j + 1;
  }
  // assert-start
  assert a[..] + b[..] == c[..];
  // assert-end

  // assert-start
  assert multiset(a[..]) + multiset(b[..]) == multiset(c[..]);
  // assert-end

// impl-end
}

method Check()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[] [1, 2, 3];
  var b := new int[] [4, 5];
  var c := new int[] [1, 2, 3, 4, 5];
  var d := join(a, b);
  // assert-start
  assert d[..] == a[..] + b[..];
  // assert-end

  // assert-start
  assert multiset(d[..]) == multiset(a[..] + b[..]);
  // assert-end

  // assert-start
  assert multiset(d[..]) == multiset(a[..]) + multiset(b[..]);
  // assert-end

  // assert-start
  assert d[..] == c[..];
  // assert-end

  // assert-start
  assert d[..] == c[..];
  // assert-end

// impl-end
}
