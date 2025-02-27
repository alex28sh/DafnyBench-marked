method FindMax(a: array<int>) returns (i: int)
  // pre-conditions-start
  requires 0 < a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < a.Length
  ensures forall k: int :: 0 <= k < a.Length ==> a[k] <= a[i]
  // post-conditions-end
{
// impl-start
  var j := 0;
  var max := a[0];
  i := 1;
  while i < a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant forall k: int :: 0 <= k < i ==> max >= a[k]
    invariant 0 <= j < a.Length
    invariant a[j] == max
    decreases a.Length - i
    // invariants-end

  {
    if max < a[i] {
      max := a[i];
      j := i;
    }
    i := i + 1;
  }
  i := j;
// impl-end
}
