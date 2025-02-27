method SwapArithmetic(X: int, Y: int)
    returns (x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x == Y
  ensures y == X
  // post-conditions-end
{
// impl-start
  x, y := X, Y;
  x := y - x;
  y := y - x;
  x := y + x;
// impl-end
}
