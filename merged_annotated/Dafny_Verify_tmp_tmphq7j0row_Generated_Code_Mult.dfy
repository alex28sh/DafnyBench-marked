method mult(a: int, b: int) returns (x: int)
  // pre-conditions-start
  requires a >= 0 && b >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures x == a * b
  // post-conditions-end
{
// impl-start
  x := 0;
  var y := a;
  while y > 0
    // invariants-start

    invariant x == (a - y) * b
    // invariants-end

  {
    x := x + b;
    y := y - 1;
  }
// impl-end
}
