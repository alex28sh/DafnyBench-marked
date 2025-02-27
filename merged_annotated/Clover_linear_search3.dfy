method LinearSearch3<T>(a: array<T>, P: T -> bool) returns (n: int)
  // pre-conditions-start
  requires exists i :: 0 <= i < a.Length && P(a[i])
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n < a.Length && P(a[n])
  ensures forall k :: 0 <= k < n ==> !P(a[k])
  // post-conditions-end
{
// impl-start
  n := 0;
  while true
    // invariants-start

    invariant 0 <= n < a.Length
    invariant exists i :: n <= i < a.Length && P(a[i])
    invariant forall k :: 0 <= k < n ==> !P(a[k])
    decreases a.Length - n
    // invariants-end

  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
// impl-end
}
