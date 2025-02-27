method main(n: int) returns (a: int, b: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures a + b == 3 * n
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  a := 0;
  b := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant a + b == 3 * i
    // invariants-end

  {
    if * {
      a := a + 1;
      b := b + 2;
    } else {
      a := a + 2;
      b := b + 1;
    }
    i := i + 1;
  }
// impl-end
}
