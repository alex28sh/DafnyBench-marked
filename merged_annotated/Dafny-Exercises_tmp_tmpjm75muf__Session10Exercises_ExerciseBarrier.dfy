method barrier(v: array<int>, p: int) returns (b: bool)
  // pre-conditions-start
  requires v.Length > 0
  requires 0 <= p < v.Length
  // pre-conditions-end
  // post-conditions-start
  ensures b == forall k, l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]
  // post-conditions-end
{
// impl-start
  var i := 1;
  var max := 0;
  while i <= p
    // invariants-start

    invariant 0 <= i <= p + 1
    invariant 0 <= max < i
    invariant forall k :: 0 <= k < i ==> v[max] >= v[k]
    decreases p - i
    // invariants-end

  {
    if v[i] > v[max] {
      max := i;
    }
    i := i + 1;
  }
  while i < v.Length && v[i] > v[max]
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant forall k :: 0 <= k <= p ==> v[k] <= v[max]
    invariant forall k :: p < k < i ==> v[k] > v[max]
    decreases v.Length - i
    // invariants-end

  {
    i := i + 1;
  }
  b := i == v.Length;
// impl-end
}
