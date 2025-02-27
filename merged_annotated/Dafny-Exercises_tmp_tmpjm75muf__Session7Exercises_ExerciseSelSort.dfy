function sorted_seg(a: array<int>, i: int, j: int): bool
  requires 0 <= i <= j <= a.Length
  reads a
{
  forall l, k :: 
    i <= l <= k < j ==>
      a[l] <= a[k]
}
// pure-end

method selSort(a: array<int>, c: int, f: int)
  // pre-conditions-start
  requires 0 <= c <= f <= a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted_seg(a, c, f)
  ensures multiset(a[c .. f]) == old(multiset(a[c .. f]))
  ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..])
  // post-conditions-end
{
// impl-start
  if c <= f - 1 {
    var i := c;
    while i < f - 1
      // invariants-start

      invariant c <= i <= f
      invariant sorted_seg(a, c, i)
      invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
      invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      decreases f - i
      // invariants-end

    {
      var less := i;
      var j := i + 1;
      while j < f
        // invariants-start

        invariant i + 1 <= j <= f
        invariant i <= less < f
        invariant sorted_seg(a, c, i)
        invariant forall k :: i <= k < j ==> a[less] <= a[k]
        invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
        invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        decreases f - j
        // invariants-end

      {
        if a[j] < a[less] {
          less := j;
        }
        j := j + 1;
      }
      a[i], a[less] := a[less], a[i];
      i := i + 1;
    }
  }
// impl-end
}
