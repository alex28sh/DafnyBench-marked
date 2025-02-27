method swap<T>(a: array<T>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i < j < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
  // post-conditions-end
{
// impl-start
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
// impl-end
}

method two_way_sort(a: array<bool>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall m, n :: 0 <= m < n < a.Length ==> !a[m] || a[n]
  ensures multiset(a[..]) == old(multiset(a[..]))
  // post-conditions-end
{
// impl-start
  var i := 0;
  var j := a.Length - 1;
  while i <= j
    // invariants-start

    invariant 0 <= i <= j + 1 <= a.Length
    invariant forall m :: 0 <= m < i ==> !a[m]
    invariant forall n :: j < n < a.Length ==> a[n]
    invariant multiset(a[..]) == old(multiset(a[..]))
    // invariants-end

  {
    if !a[i] {
      i := i + 1;
    } else if a[j] {
      j := j - 1;
    } else {
      swap(a, i, j);
      i := i + 1;
      j := j - 1;
    }
  }
// impl-end
}
