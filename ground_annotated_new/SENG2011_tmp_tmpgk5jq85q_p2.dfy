method AbsIt(s: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies s
  ensures forall x :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
  ensures forall x :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  while i < s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> old(s[k]) < 0 ==> s[k] == -old(s[k])
    invariant forall k :: 0 <= k < i ==> old(s[k]) >= 0 ==> s[k] == old(s[k])
    invariant forall k :: i <= k < s.Length ==> old(s[k]) == s[k]
    // invariants-end

  {
    if s[i] < 0 {
      s[i] := -s[i];
    }
    i := i + 1;
  }
// impl-end
}
