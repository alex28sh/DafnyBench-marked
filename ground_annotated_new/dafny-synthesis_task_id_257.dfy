method Swap(a: int, b: int) returns (result: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == 2
  ensures result[0] == b
  ensures result[1] == a
  // post-conditions-end
{
// impl-start
  result := [b, a];
// impl-end
}
