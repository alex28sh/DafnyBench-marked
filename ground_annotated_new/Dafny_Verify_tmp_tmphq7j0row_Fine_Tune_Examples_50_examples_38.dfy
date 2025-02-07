method main(n: int)
    returns (i: int, x: int, y: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures i % 2 != 0 || x == 2 * y
  // post-conditions-end
{
// impl-start
  i := 0;
  x := 0;
  y := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant x == i
    invariant y == i / 2
    // invariants-end

  {
    i := i + 1;
    x := x + 1;
    if i % 2 == 0 {
      y := y + 1;
    } else {
    }
  }
// impl-end
}
