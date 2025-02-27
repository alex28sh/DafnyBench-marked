function sorted(a: array<int>): bool
  requires a != null
  reads a
{
  forall j, k :: 
    0 <= j < k < a.Length ==>
      a[j] <= a[k]
}
// pure-end

method BinarySearch(a: array<int>, value: int) returns (index: int)
  // pre-conditions-start
  requires a != null && 0 <= a.Length && sorted(a)
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
  // post-conditions-end
{
// impl-start
  var low, high := 0, a.Length;
  while low < high
    // invariants-start

    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
    decreases high - low
    // invariants-end

  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
// impl-end
}
