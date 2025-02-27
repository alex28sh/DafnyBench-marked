method findMax(a: array<int>, n: int) returns (r: int)
  // pre-conditions-start
  requires a.Length > 0
  requires 0 < n <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= r < n <= a.Length
  ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k]
  ensures multiset(a[..]) == multiset(old(a[..]))
  // post-conditions-end
{
// impl-start
  var mi;
  var i;
  mi := 0;
  i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n <= a.Length
    invariant 0 <= mi < n
    invariant forall k :: 0 <= k < i ==> a[mi] >= a[k]
    decreases n - i
    // invariants-end

  {
    if a[i] > a[mi] {
      mi := i;
    }
    i := i + 1;
  }
  return mi;
// impl-end
}
