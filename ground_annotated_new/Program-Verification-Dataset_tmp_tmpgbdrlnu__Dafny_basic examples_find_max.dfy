method FindMax(a: array<int>) returns (max: int)
  // pre-conditions-start
  requires a != null && a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= max < a.Length
  ensures forall x :: 0 <= x < a.Length ==> a[max] >= a[x]
  // post-conditions-end
{
// impl-start
  var i := 0;
  max := 0;
  while i < a.Length
    // invariants-start

    invariant i <= a.Length
    invariant 0 <= max
    invariant max == 0 || 0 < max < i
    invariant forall k :: 0 <= k < i ==> a[max] >= a[k]
    // invariants-end

  {
    if a[i] > a[max] {
      max := i;
    }
    i := i + 1;
  }
  return max;
// impl-end
}
