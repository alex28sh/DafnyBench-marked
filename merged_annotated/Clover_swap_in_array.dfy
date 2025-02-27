method swap(arr: array<int>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i < arr.Length && 0 <= j < arr.Length
  // pre-conditions-end
  // post-conditions-start
  modifies arr
  ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
  ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
  // post-conditions-end
{
// impl-start
  var tmp := arr[i];
  arr[i] := arr[j];
  arr[j] := tmp;
// impl-end
}
