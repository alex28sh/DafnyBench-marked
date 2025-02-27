method BinarySearch(arr: array<int>, target: int) returns (index: int)
  // pre-conditions-start
  requires distinct(arr)
  requires sorted(arr)
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= index < arr.Length
  ensures index == -1 ==> not_found(arr, target)
  ensures index != -1 ==> found(arr, target, index)
  // post-conditions-end
{
// impl-start
  var low, high := 0, arr.Length - 1;
  while low <= high
    // invariants-start

    invariant 0 <= low <= high + 1
    invariant low - 1 <= high < arr.Length
    invariant forall i :: 0 <= i <= low && high <= i < arr.Length ==> arr[i] != target
    // invariants-end

  {
    var mid := (low + high) / 2;
    if arr[mid] == target {
      return mid;
    } else if arr[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  return -1;
// impl-end
}

function sorted(a: array<int>): bool
  reads a
{
  forall j, k :: 
    0 <= j < k < a.Length ==>
      a[j] <= a[k]
}
// pure-end

function distinct(arr: array<int>): bool
  reads arr
{
  forall i, j :: 
    0 <= i < arr.Length &&
    0 <= j < arr.Length ==>
      arr[i] != arr[j]
}
// pure-end

function not_found(arr: array<int>, target: int): bool
  reads arr
{
  forall j :: 
    0 <= j < arr.Length ==>
      arr[j] != target
}
// pure-end

function found(arr: array<int>, target: int, index: int): bool
  requires -1 <= index < arr.Length
  reads arr
{
  if index == -1 then
    false
  else if arr[index] == target then
    true
  else
    false
}
// pure-end
