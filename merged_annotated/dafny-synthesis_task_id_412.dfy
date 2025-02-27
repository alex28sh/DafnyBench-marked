function IsEven(n: int): bool
{
  n % 2 == 0
}
// pure-end

method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
  ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
  // post-conditions-end
{
// impl-start
  evenList := [];
  for i := 0 to arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant 0 <= |evenList| <= i
    invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k]) && evenList[k] in arr[..]
    invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> arr[k] in evenList
    // invariants-end

  {
    if IsEven(arr[i]) {
      evenList := evenList + [arr[i]];
    }
  }
// impl-end
}
