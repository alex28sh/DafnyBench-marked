method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)
  // pre-conditions-start
  requires arr != null
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index < arr.Length ==> arr[index] == target
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
  // post-conditions-end
{
// impl-start
  index := -1;
  for i := 0 to arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant index == -1 ==> forall k :: 0 <= k < i ==> arr[k] != target
    invariant 0 <= index < i ==> arr[index] == target
    invariant forall k :: 0 <= k < arr.Length ==> arr[k] == old(arr[k])
    // invariants-end

  {
    if arr[i] == target {
      index := i;
      break;
    }
    if arr[i] > target {
      break;
    }
  }
// impl-end
}
