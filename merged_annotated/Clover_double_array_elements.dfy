method double_array_elements(s: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant forall x :: i <= x < s.Length ==> s[x] == old(s[x])
    invariant forall x :: 0 <= x < i ==> s[x] == 2 * old(s[x])
    // invariants-end

  {
    s[i] := 2 * s[i];
    i := i + 1;
  }
// impl-end
}
