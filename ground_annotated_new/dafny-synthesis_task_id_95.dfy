method SmallestListLength(s: seq<seq<int>>) returns (v: int)
  // pre-conditions-start
  requires |s| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
  ensures exists i :: 0 <= i < |s| && v == |s[i]|
  // post-conditions-end
{
// impl-start
  v := |s[0]|;
  for i := 1 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> v <= |s[k]|
    invariant exists k :: 0 <= k < i && v == |s[k]|
    // invariants-end

  {
    if |s[i]| < v {
      v := |s[i]|;
    }
  }
// impl-end
}
