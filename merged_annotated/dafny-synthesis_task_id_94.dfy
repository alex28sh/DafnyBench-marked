method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
  // pre-conditions-start
  requires s.Length > 0
  requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1]
  // post-conditions-end
{
// impl-start
  var minSecondIndex := 0;
  for i := 1 to s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant 0 <= minSecondIndex < i
    invariant forall j :: 0 <= j < i ==> s[minSecondIndex][1] <= s[j][1]
    // invariants-end

  {
    if s[i][1] < s[minSecondIndex][1] {
      minSecondIndex := i;
    }
  }
  firstOfMinSecond := s[minSecondIndex][0];
// impl-end
}
