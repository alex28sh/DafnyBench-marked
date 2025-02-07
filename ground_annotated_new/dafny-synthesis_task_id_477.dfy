function IsUpperCase(c: char): bool
{
  65 <= c as int <= 90
}
// pure-end

function IsUpperLowerPair(C: char, c: char): bool
{
  C as int == c as int - 32
}
// pure-end

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}
// pure-end

method ToLowercase(s: string) returns (v: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
  // post-conditions-end
{
// impl-start
  var s': string := [];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    // invariants-end

  {
    if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
// impl-end
}
