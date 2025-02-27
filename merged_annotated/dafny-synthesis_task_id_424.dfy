method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
  // post-conditions-end
{
// impl-start
  var rearChars: seq<char> := [];
  for i := 0 to |l|
    // invariants-start

    invariant 0 <= i <= |l|
    invariant |rearChars| == i
    invariant forall k :: 0 <= k < i ==> rearChars[k] == l[k][|l[k]| - 1]
    // invariants-end

  {
    rearChars := rearChars + [l[i][|l[i]| - 1]];
  }
  return rearChars;
// impl-end
}
