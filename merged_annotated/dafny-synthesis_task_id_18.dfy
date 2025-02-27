method RemoveChars(s1: string, s2: string) returns (v: string)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |v| <= |s1|
  ensures forall i :: 0 <= i < |v| ==> v[i] in s1 && !(v[i] in s2)
  ensures forall i :: 0 <= i < |s1| ==> s1[i] in s2 || s1[i] in v
  // post-conditions-end
{
// impl-start
  var v': string := [];
  for i := 0 to |s1|
    // invariants-start

    invariant 0 <= i <= |s1|
    invariant |v'| <= i
    invariant forall k :: 0 <= k < |v'| ==> v'[k] in s1 && !(v'[k] in s2)
    invariant forall k :: 0 <= k < i ==> s1[k] in s2 || s1[k] in v'
    // invariants-end

  {
    if !(s1[i] in s2) {
      v' := v' + [s1[i]];
    }
  }
  return v';
// impl-end
}
