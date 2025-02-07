method CountNonEmptySubstrings(s: string) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
  // post-conditions-end
{
// impl-start
  count := |s| * (|s| + 1) / 2;
// impl-end
}
