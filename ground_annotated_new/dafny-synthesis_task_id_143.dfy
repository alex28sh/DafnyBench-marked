method CountArrays(arrays: seq<array<int>>) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |arrays|
  // post-conditions-end
{
// impl-start
  count := |arrays|;
// impl-end
}
