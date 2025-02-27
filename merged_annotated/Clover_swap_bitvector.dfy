method SwapBitvectors(X: bv8, Y: bv8)
    returns (x: bv8, y: bv8)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x == Y
  ensures y == X
  // post-conditions-end
{
// impl-start
  x, y := X, Y;
  x := x ^ y;
  y := x ^ y;
  x := x ^ y;
// impl-end
}
