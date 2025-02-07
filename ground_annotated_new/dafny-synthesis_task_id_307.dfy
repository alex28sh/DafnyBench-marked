method DeepCopySeq(s: seq<int>) returns (copy: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |copy| == |s|
  ensures forall i :: 0 <= i < |s| ==> copy[i] == s[i]
  // post-conditions-end
{
// impl-start
  var newSeq: seq<int> := [];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant |newSeq| == i
    invariant forall k :: 0 <= k < i ==> newSeq[k] == s[k]
    // invariants-end

  {
    newSeq := newSeq + [s[i]];
  }
  return newSeq;
// impl-end
}
