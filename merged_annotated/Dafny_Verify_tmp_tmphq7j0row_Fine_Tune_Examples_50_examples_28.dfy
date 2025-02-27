method main(x: int, y: int)
    returns (x_out: int, y_out: int, n: int)
  // pre-conditions-start
  requires x >= 0
  requires y >= 0
  requires x == y
  // pre-conditions-end
  // post-conditions-start
  ensures y_out == n
  // post-conditions-end
{
// impl-start
  x_out := x;
  y_out := y;
  n := 0;
  while x_out != n
    // invariants-start

    invariant x_out >= 0
    invariant x_out == y_out
    // invariants-end

  {
    x_out := x_out - 1;
    y_out := y_out - 1;
  }
// impl-end
}
