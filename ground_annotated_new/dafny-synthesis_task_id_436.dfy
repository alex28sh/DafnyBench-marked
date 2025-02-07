function IsNegative(n: int): bool
{
  n < 0
}
// pure-end

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
  ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
  // post-conditions-end
{
// impl-start
  negativeList := [];
  for i := 0 to arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant 0 <= |negativeList| <= i
    invariant forall k :: 0 <= k < |negativeList| ==> IsNegative(negativeList[k]) && negativeList[k] in arr[..]
    invariant forall k :: 0 <= k < i && IsNegative(arr[k]) ==> arr[k] in negativeList
    // invariants-end

  {
    if IsNegative(arr[i]) {
      negativeList := negativeList + [arr[i]];
    }
  }
// impl-end
}
