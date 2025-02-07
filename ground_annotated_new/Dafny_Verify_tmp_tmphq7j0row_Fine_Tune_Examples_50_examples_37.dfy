method main(n: int) returns (x: int, m: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures n <= 0 || (0 <= m && m < n)
  // post-conditions-end
{
// impl-start
  x := 0;
  m := 0;
  while x < n
    // invariants-start

    invariant 0 <= x <= n
    invariant 0 <= m < n
    // invariants-end

  {
    if * {
      m := x;
    } else {
    }
    x := x + 1;
  }
// impl-end
}
