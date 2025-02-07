method CountLists(lists: seq<seq<int>>) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |lists|
  // post-conditions-end
{
// impl-start
  count := |lists|;
// impl-end
}
