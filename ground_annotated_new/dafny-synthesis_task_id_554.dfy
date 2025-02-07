function IsOdd(n: int): bool
{
  n % 2 == 1
}
// pure-end

method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
  ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
  // post-conditions-end
{
// impl-start
  oddList := [];
  for i := 0 to arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant 0 <= |oddList| <= i
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k]) && oddList[k] in arr[..]
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
    // invariants-end

  {
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
  }
// impl-end
}
