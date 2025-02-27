function sorted_seg(a: array<int>, i: int, j: int): bool
  requires 0 <= i <= j <= a.Length
  reads a
{
  forall l, k :: 
    i <= l <= k < j ==>
      a[l] <= a[k]
}
// pure-end

method bubbleSorta(a: array<int>, c: int, f: int)
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
  var i := c;
  while i < f
    // invariants-start

    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
    invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    decreases a.Length - i
    // invariants-end

  {
    var j := f - 1;
    // assert-start
    assert multiset(a[c .. f]) == old(multiset(a[c .. f]));
    // assert-end

    while j > i
      // invariants-start

      invariant i <= j <= f - 1
      invariant forall k :: j <= k <= f - 1 ==> a[j] <= a[k]
      invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
      invariant sorted_seg(a, c, i)
      invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      decreases j - i
      // invariants-end

    {
      if a[j - 1] > a[j] {
        a[j], a[j - 1] := a[j - 1], a[j];
      }
      j := j - 1;
    }
    // assert-start
    assert sorted_seg(a, c, i + 1);
    // assert-end

    // assert-start
    assert forall k :: i < k < f ==> a[i] <= a[k];
    // assert-end

    i := i + 1;
  }
// impl-end
}

method bubbleSort(a: array<int>, c: int, f: int)
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
  var i := c;
  var b := true;
  while i < f && b
    // invariants-start

    invariant c <= i <= f
    invariant sorted_seg(a, c, i)
    invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
    invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
    invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
    invariant !b ==> sorted_seg(a, i, f)
    decreases a.Length - i
    // invariants-end

  {
    var j := f - 1;
    b := false;
    // assert-start
    assert multiset(a[c .. f]) == old(multiset(a[c .. f]));
    // assert-end

    while j > i
      // invariants-start

      invariant i <= j <= f - 1
      invariant forall k :: j <= k <= f - 1 ==> a[j] <= a[k]
      invariant forall k, l :: c <= k < i && i <= l < f ==> a[k] <= a[l]
      invariant sorted_seg(a, c, i)
      invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
      invariant !b ==> sorted_seg(a, j, f)
      invariant multiset(a[c .. f]) == old(multiset(a[c .. f]))
      decreases j - i
      // invariants-end

    {
      if a[j - 1] > a[j] {
        a[j], a[j - 1] := a[j - 1], a[j];
        b := true;
      }
      j := j - 1;
    }
    // assert-start
    assert !b ==> sorted_seg(a, i, f);
    // assert-end

    i := i + 1;
  }
// impl-end
}
