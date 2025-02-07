method SplitArray(arr: array<int>, L: int)
    returns (firstPart: seq<int>, secondPart: seq<int>)
  // pre-conditions-start
  requires 0 <= L <= arr.Length
  // pre-conditions-end
  // post-conditions-start
  ensures |firstPart| == L
  ensures |secondPart| == arr.Length - L
  ensures firstPart + secondPart == arr[..]
  // post-conditions-end
{
// impl-start
  firstPart := arr[..L];
  secondPart := arr[L..];
// impl-end
}
