method MinLengthSublist(s: seq<seq<int>>) returns (minSublist: seq<int>)
  // pre-conditions-start
  requires |s| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures minSublist in s
  ensures forall sublist :: sublist in s ==> |minSublist| <= |sublist|
  // post-conditions-end
{
// impl-start
  minSublist := s[0];
  for i := 1 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    invariant minSublist in s[..i]
    invariant forall sublist :: sublist in s[..i] ==> |minSublist| <= |sublist|
    // invariants-end

  {
    if |s[i]| < |minSublist| {
      minSublist := s[i];
    }
  }
// impl-end
}
