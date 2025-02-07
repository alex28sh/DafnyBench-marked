method MedianLength(a: int, b: int) returns (median: int)
  // pre-conditions-start
  requires a > 0 && b > 0
  // pre-conditions-end
  // post-conditions-start
  ensures median == (a + b) / 2
  // post-conditions-end
{
// impl-start
  median := (a + b) / 2;
// impl-end
}
