method ToCharArray(s: string) returns (a: array<char>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length == |s|
  ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
  // post-conditions-end
{
// impl-start
  a := new char[|s|];
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant a.Length == |s|
    invariant forall k :: 0 <= k < i ==> a[k] == s[k]
    // invariants-end

  {
    a[i] := s[i];
  }
// impl-end
}
