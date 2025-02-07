function InsertionSorted(Array: array<int>, left: int, right: int): bool
  requires 0 <= left <= right <= Array.Length
  reads Array
{
  forall i, j :: 
    left <= i < j < right ==>
      Array[i] <= Array[j]
}
// pure-end

method sorting(Array: array<int>)
  // pre-conditions-start
  requires Array.Length > 1
  // pre-conditions-end
  // post-conditions-start
  modifies Array
  ensures InsertionSorted(Array, 0, Array.Length)
  // post-conditions-end
{
// impl-start
  var high := 1;
  while high < Array.Length
    // invariants-start

    invariant 1 <= high <= Array.Length
    invariant InsertionSorted(Array, 0, high)
    // invariants-end

  {
    var low := high - 1;
    while low >= 0 && Array[low + 1] < Array[low]
      // invariants-start

      invariant forall idx, idx' :: 0 <= idx < idx' < high + 1 && idx' != low + 1 ==> Array[idx] <= Array[idx']
      // invariants-end

    {
      Array[low], Array[low + 1] := Array[low + 1], Array[low];
      low := low - 1;
    }
    high := high + 1;
  }
// impl-end
}
