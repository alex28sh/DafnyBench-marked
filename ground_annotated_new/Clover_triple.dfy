method Triple(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  r := x * 3;
// impl-end
}
