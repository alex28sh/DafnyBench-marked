method Minimum(a: array<int>) returns (m: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures exists i :: 0 <= i < a.Length && m == a[i]
  ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
  // post-conditions-end
{
// impl-start
  var n := 0;
  m := a[0];
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant exists i :: 0 <= i < a.Length && m == a[i]
    invariant forall i :: 0 <= i < n ==> m <= a[i]
    // invariants-end

  {
    if a[n] < m {
      m := a[n];
    }
    n := n + 1;
  }
// impl-end
}
