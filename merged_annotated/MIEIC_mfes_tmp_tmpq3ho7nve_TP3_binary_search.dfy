function isSorted(a: array<int>): bool
  reads a
{
  forall i, j :: 
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}
// pure-end

method binarySearch(a: array<int>, x: int) returns (index: int)
  // pre-conditions-start
  requires isSorted(a)
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= index < a.Length
  ensures if index != -1 then a[index] == x else x !in a[..]
  // post-conditions-end
{
// impl-start
  var low, high := 0, a.Length;
  while low < high
    // invariants-start

    invariant 0 <= low <= high <= a.Length && x !in a[..low] && x !in a[high..]
    decreases high - low
    // invariants-end

  {
    var mid := low + (high - low) / 2;
    if {
      case a[mid] < x =>
        low := mid + 1;
      case a[mid] > x =>
        high := mid;
      case a[mid] == x =>
        return mid;
    }
  }
  return -1;
// impl-end
}

method testBinarySearch()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[] [1, 4, 4, 6, 8];
  // assert-start
  assert a[..] == [1, 4, 4, 6, 8];
  // assert-end

  var id1 := binarySearch(a, 6);
  // assert-start
  assert a[3] == 6;
  // assert-end

  // assert-start
  assert id1 == 3;
  // assert-end

  var id2 := binarySearch(a, 3);
  // assert-start
  assert id2 == -1;
  // assert-end

  var id3 := binarySearch(a, 4);
  // assert-start
  assert a[1] == 4 && a[2] == 4;
  // assert-end

  // assert-start
  assert id3 in {1, 2};
  // assert-end

// impl-end
}
