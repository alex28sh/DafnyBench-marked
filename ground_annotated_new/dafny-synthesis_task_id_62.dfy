method FindSmallest(s: array<int>) returns (min: int)
  // pre-conditions-start
  requires s.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
  // post-conditions-end
{
// impl-start
  min := s[0];
  for i := 1 to s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant forall k :: 0 <= k < i ==> min <= s[k]
    invariant exists k :: 0 <= k < i && min == s[k]
    // invariants-end

  {
    if s[i] < min {
      min := s[i];
    }
  }
// impl-end
}
