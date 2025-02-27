method FindMax(a: array<int>) returns (i: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
  // post-conditions-end
{
// impl-start
  i := 0;
  var index := 1;
  while index < a.Length
    // invariants-start

    invariant 0 < index <= a.Length
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
    // invariants-end

  {
    if a[index] > a[i] {
      i := index;
    }
    index := index + 1;
  }
// impl-end
}
