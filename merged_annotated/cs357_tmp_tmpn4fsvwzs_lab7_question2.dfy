method Two(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y == x + 1
  // post-conditions-end
{
// impl-start
  // assert-start
  assert true;
  // assert-end

  var a := x + 1;
  // assert-start
  assert (a - 1 == 0 ==> x == 0) && (x - 1 != 0 ==> a == x + 1);
  // assert-end

  if a - 1 == 0 {
    y := 1;
  } else {
    y := a;
  }
// impl-end
}
