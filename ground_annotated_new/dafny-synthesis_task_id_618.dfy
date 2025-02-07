method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |a| == |b|
  requires forall i :: 0 <= i < |b| ==> b[i] != 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
  // post-conditions-end
{
// impl-start
  result := [];
  for i := 0 to |a|
    // invariants-start

    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] / b[k]
    // invariants-end

  {
    result := result + [a[i] / b[i]];
  }
// impl-end
}
