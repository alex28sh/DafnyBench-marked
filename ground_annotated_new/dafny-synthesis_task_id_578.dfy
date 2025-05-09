method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>)
    returns (r: seq<int>)
  // pre-conditions-start
  requires |s1| == |s2| && |s2| == |s3|
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == 3 * |s1|
  ensures forall i :: 0 <= i < |s1| ==> r[3 * i] == s1[i] && r[3 * i + 1] == s2[i] && r[3 * i + 2] == s3[i]
  // post-conditions-end
{
// impl-start
  r := [];
  for i := 0 to |s1|
    // invariants-start

    invariant 0 <= i <= |s1|
    invariant |r| == 3 * i
    invariant forall k :: 0 <= k < i ==> r[3 * k] == s1[k] && r[3 * k + 1] == s2[k] && r[3 * k + 2] == s3[k]
    // invariants-end

  {
    r := r + [s1[i], s2[i], s3[i]];
  }
// impl-end
}
