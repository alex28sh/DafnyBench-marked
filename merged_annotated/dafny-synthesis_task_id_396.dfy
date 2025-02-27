method StartAndEndWithSameChar(s: string) returns (result: bool)
  // pre-conditions-start
  requires |s| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> s[0] == s[|s| - 1]
  // post-conditions-end
{
// impl-start
  result := s[0] == s[|s| - 1];
// impl-end
}
