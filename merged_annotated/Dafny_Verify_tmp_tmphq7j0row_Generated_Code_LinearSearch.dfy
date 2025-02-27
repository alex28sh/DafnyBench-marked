method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= a.Length
  ensures n == a.Length || P(a[n])
  ensures forall i :: 0 <= i < n ==> !P(a[i])
  // post-conditions-end
{
// impl-start
  n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    // invariants-end

  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
// impl-end
}
