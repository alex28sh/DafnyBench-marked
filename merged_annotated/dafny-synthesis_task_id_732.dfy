function IsSpaceCommaDot(c: char): bool
{
  c == ' ' || c == ',' || c == '.'
}
// pure-end

method ReplaceWithColon(s: string) returns (v: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
  // post-conditions-end
{
// impl-start
  var s': string := [];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
    // invariants-end

  {
    if IsSpaceCommaDot(s[i]) {
      s' := s' + [':'];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
// impl-end
}
