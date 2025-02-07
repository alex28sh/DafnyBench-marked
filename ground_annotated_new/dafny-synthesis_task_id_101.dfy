method KthElement(arr: array<int>, k: int) returns (result: int)
  // pre-conditions-start
  requires 1 <= k <= arr.Length
  // pre-conditions-end
  // post-conditions-start
  ensures result == arr[k - 1]
  // post-conditions-end
{
// impl-start
  result := arr[k - 1];
// impl-end
}
