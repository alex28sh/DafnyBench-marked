method SelectionSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
    invariant multiset(a[..]) == old(multiset(a[..]))
    // invariants-end

  {
    var mindex, m := n, n + 1;
    while m != a.Length
      // invariants-start

      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
      // invariants-end

    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
// impl-end
}
