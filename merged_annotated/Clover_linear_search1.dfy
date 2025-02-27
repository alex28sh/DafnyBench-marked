method LinearSearch(a: array<int>, e: int) returns (n: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == e
  ensures forall i :: 0 <= i < n ==> e != a[i]
  // post-conditions-end
{
// impl-start
  n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> e != a[i]
    // invariants-end

  {
    if e == a[n] {
      return;
    }
    n := n + 1;
  }
// impl-end
}
