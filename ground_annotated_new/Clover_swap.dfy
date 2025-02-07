method Swap(X: int, Y: int)
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
  var tmp := x;
  x := y;
  y := tmp;
  // assert-start
  assert x == Y && y == X;
  // assert-end

// impl-end
}
