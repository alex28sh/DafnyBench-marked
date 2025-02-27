method SwapFirstAndLast(a: array<int>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[0] == old(a[a.Length - 1])
  ensures a[a.Length - 1] == old(a[0])
  ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
  // post-conditions-end
{
// impl-start
  var tmp := a[0];
  a[0] := a[a.Length - 1];
  a[a.Length - 1] := tmp;
// impl-end
}
