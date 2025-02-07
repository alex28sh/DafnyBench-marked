function sorted(a: array<T>, n: nat): bool
  requires n <= a.Length
  reads a
{
  forall i, j :: 
    0 <= i < j < n ==>
      a[i] <= a[j]
}
// pure-end

method binarySearch(a: array<T>, x: T) returns (index: int)
  // pre-conditions-start
  requires sorted(a, a.Length)
  // pre-conditions-end
  // post-conditions-start
  ensures sorted(a, a.Length)
  ensures 0 <= index <= a.Length
  ensures index > 0 ==> a[index - 1] <= x
  ensures index < a.Length ==> a[index] >= x
  // post-conditions-end
{
// impl-start
  var low, high := 0, a.Length;
  while low < high
    // invariants-start

    invariant 0 <= low <= high <= a.Length
    invariant low > 0 ==> a[low - 1] <= x
    invariant high < a.Length ==> a[high] >= x
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
  return low;
// impl-end
}

method testBinarySearch()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[2] [1, 3];
  var id0 := binarySearch(a, 0);
  // assert-start
  assert id0 == 0;
  // assert-end

  var id1 := binarySearch(a, 1);
  // assert-start
  assert id1 in {0, 1};
  // assert-end

  var id2 := binarySearch(a, 2);
  // assert-start
  assert id2 == 1;
  // assert-end

  var id3 := binarySearch(a, 3);
  // assert-start
  assert id3 in {1, 2};
  // assert-end

  var id4 := binarySearch(a, 4);
  // assert-start
  assert id4 == 2;
  // assert-end

// impl-end
}

type T = int
