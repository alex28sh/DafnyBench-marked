method replace(arr: array<int>, k: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies arr
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) > k ==> arr[i] == -1
  ensures forall i :: 0 <= i < arr.Length ==> old(arr[i]) <= k ==> arr[i] == old(arr[i])
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> old(arr[j]) > k ==> arr[j] == -1
    invariant forall j :: 0 <= j < i ==> old(arr[j]) <= k ==> arr[j] == old(arr[j])
    invariant forall j :: i <= j < arr.Length ==> old(arr[j]) == arr[j]
    decreases arr.Length - i
    // invariants-end

  {
    if arr[i] > k {
      arr[i] := -1;
    }
    i := i + 1;
  }
// impl-end
}
