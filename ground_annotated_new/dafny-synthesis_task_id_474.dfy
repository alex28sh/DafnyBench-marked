method ReplaceChars(s: string, oldChar: char, newChar: char)
    returns (v: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
  // post-conditions-end
{
// impl-start
  var s': string := [];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> s'[k] == newChar) && (s[k] != oldChar ==> s'[k] == s[k])
    // invariants-end

  {
    if s[i] == oldChar {
      s' := s' + [newChar];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
// impl-end
}
