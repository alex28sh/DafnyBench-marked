method RotateRight(a: array)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i - 1])
  ensures a[0] == old(a[a.Length - 1])
  // post-conditions-end
{
// impl-start
  var n := 1;
  while n != a.Length
    // invariants-start

    invariant 1 <= n <= a.Length
    invariant forall i :: 1 <= i < n ==> a[i] == old(a[i - 1])
    invariant a[0] == old(a[n - 1])
    invariant forall i :: n <= i <= a.Length - 1 ==> a[i] == old(a[i])
    // invariants-end

  {
    a[0], a[n] := a[n], a[0];
    n := n + 1;
  }
// impl-end
}
