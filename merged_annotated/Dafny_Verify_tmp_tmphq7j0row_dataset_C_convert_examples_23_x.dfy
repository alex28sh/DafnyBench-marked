method main(n: int) returns (sum: int, i: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  sum := 0;
  i := 0;
  while i < n
    // invariants-start

    invariant sum >= 0
    invariant 0 <= i <= n
    // invariants-end

  {
    sum := sum + i;
    i := i + 1;
  }
// impl-end
}
