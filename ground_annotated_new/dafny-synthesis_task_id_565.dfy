method SplitStringIntoChars(s: string) returns (v: seq<char>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
  // post-conditions-end
{
// impl-start
  v := [];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> v[k] == s[k]
    // invariants-end

  {
    v := v + [s[i]];
  }
// impl-end
}
