method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
  // post-conditions-end
{
// impl-start
  var rotated: seq<int> := [];
  for i := 0 to |l|
    // invariants-start

    invariant 0 <= i <= |l|
    invariant |rotated| == i
    invariant forall k :: 0 <= k < i ==> rotated[k] == l[(k - n + |l|) % |l|]
    // invariants-end

  {
    rotated := rotated + [l[(i - n + |l|) % |l|]];
  }
  return rotated;
// impl-end
}
