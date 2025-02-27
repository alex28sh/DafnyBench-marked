method DoubleQuadruple(x: int) returns (a: int, b: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == 2 * x && b == 4 * x
  // post-conditions-end
{
// impl-start
  a := 2 * x;
  b := 2 * a;
// impl-end
}
