method reverse(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length / 2
    // invariants-start

    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i || a.Length - 1 - i < k <= a.Length - 1 ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: i <= k <= a.Length - 1 - i ==> a[k] == old(a[k])
    // invariants-end

  {
    a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
    i := i + 1;
  }
// impl-end
}
