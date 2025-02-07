method main(x: int) returns (j: int, i: int)
  // pre-conditions-start
  requires x > 0
  // pre-conditions-end
  // post-conditions-start
  ensures j == 2 * x
  // post-conditions-end
{
// impl-start
  i := 0;
  j := 0;
  while i < x
    // invariants-start

    invariant 0 <= i <= x
    invariant j == 2 * i
    // invariants-end

  {
    j := j + 2;
    i := i + 1;
  }
// impl-end
}
