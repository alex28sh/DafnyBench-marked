method main()
    returns (t1: int, t2: int, x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y >= 1
  // post-conditions-end
{
// impl-start
  x := 1;
  y := 1;
  t1 := 0;
  t2 := 0;
  while x <= 100000
    // invariants-start

    invariant x == y
    // invariants-end

  {
    t1 := x;
    t2 := y;
    x := t1 + t2;
    y := t1 + t2;
  }
// impl-end
}
