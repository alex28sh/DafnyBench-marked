method CountCharacters(s: string) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |s|
  // post-conditions-end
{
// impl-start
  count := |s|;
// impl-end
}
