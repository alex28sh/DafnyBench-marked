method M1(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == x * y
  decreases x < 0, x
  // post-conditions-end
{
// impl-start
  if x == 0 {
    r := 0;
  } else if x < 0 {
    r := M1(-x, y);
    r := -r;
  } else {
    r := M1(x - 1, y);
    r := A1(r, y);
  }
// impl-end
}

method A1(x: int, y: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == x + y
  // post-conditions-end
{
// impl-start
  r := x;
  if y < 0 {
    var n := y;
    while n != 0
      // invariants-start

      invariant r == x + y - n
      invariant -n >= 0
      // invariants-end

    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while n != 0
      // invariants-start

      invariant r == x + y - n
      invariant n >= 0
      // invariants-end

    {
      r := r + 1;
      n := n - 1;
    }
  }
// impl-end
}
