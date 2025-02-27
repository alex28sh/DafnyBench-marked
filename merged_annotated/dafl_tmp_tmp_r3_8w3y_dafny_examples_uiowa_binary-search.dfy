function isSorted(a: array<int>): bool
  reads a
{
  forall i: nat, j: nat :: 
    i <= j < a.Length ==>
      a[i] <= a[j]
}
// pure-end

method binSearch(a: array<int>, K: int) returns (b: bool)
  // pre-conditions-start
  requires isSorted(a)
  // pre-conditions-end
  // post-conditions-start
  ensures b == exists i: nat :: i < a.Length && a[i] == K
  // post-conditions-end
{
// impl-start
  var lo: nat := 0;
  var hi: nat := a.Length;
  while lo < hi
    // invariants-start

    invariant 0 <= lo <= hi <= a.Length
    invariant forall i: nat :: i < lo || hi <= i < a.Length ==> a[i] != K
    decreases hi - lo
    // invariants-end

  {
    var mid: nat := (lo + hi) / 2;
    // assert-start
    assert lo <= mid <= hi;
    // assert-end

    if a[mid] < K {
      // assert-start
      assert a[lo] <= a[mid];
      // assert-end

      // assert-start
      assert a[mid] < K;
      // assert-end

      lo := mid + 1;
      // assert-start
      assert mid < lo <= hi;
      // assert-end

    } else if a[mid] > K {
      // assert-start
      assert K < a[mid];
      // assert-end

      hi := mid;
      // assert-start
      assert lo <= hi == mid;
      // assert-end

    } else {
      return true;
      // assert-start
      assert a[mid] == K;
      // assert-end

    }
  }
  return false;
// impl-end
}
