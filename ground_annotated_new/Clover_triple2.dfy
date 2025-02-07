method Triple(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  if {
    case x < 18 =>
      var a, b := 2 * x, 4 * x;
      r := (a + b) / 2;
    case 0 <= x =>
      var y := 2 * x;
      r := x + y;
  }
// impl-end
}
