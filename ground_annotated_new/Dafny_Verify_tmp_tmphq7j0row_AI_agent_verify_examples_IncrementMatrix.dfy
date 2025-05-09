method IncrementMatrix(a: array2<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
  // post-conditions-end
{
// impl-start
  var m := 0;
  while m != a.Length0
    // invariants-start

    invariant 0 <= m <= a.Length0
    invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
    invariant forall i, j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j])
    // invariants-end

  {
    var n := 0;
    while n != a.Length1
      // invariants-start

      invariant 0 <= n <= a.Length1
      invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
      invariant forall i, j :: m < i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j])
      invariant forall j :: 0 <= j < n ==> a[m, j] == old(a[m, j]) + 1
      invariant forall j :: n <= j < a.Length1 ==> a[m, j] == old(a[m, j])
      // invariants-end

    {
      a[m, n] := a[m, n] + 1;
      n := n + 1;
    }
    m := m + 1;
  }
// impl-end
}
