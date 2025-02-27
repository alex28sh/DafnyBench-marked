function sorted(a: array?<int>, l: int, u: int): bool
  requires a != null
  reads a
{
  forall i, j :: 
    0 <= l <= i <= j <= u < a.Length ==>
      a[i] <= a[j]
}
// pure-end

method BinarySearch(a: array?<int>, key: int) returns (index: int)
  // pre-conditions-start
  requires a != null && sorted(a, 0, a.Length - 1)
  // pre-conditions-end
  // post-conditions-start
  ensures index >= 0 ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  // post-conditions-end
{
// impl-start
  var low := 0;
  var high := a.Length;
  while low < high
    // invariants-start

    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != key
    // invariants-end

  {
    var mid := (low + high) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else if key < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
// impl-end
}
