method Triple(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  if x == 0 {
    r := 0;
  } else {
    var y := 2 * x;
    r := x + y;
  }
// impl-end
}
