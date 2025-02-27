method main(n: int, k: int)
    returns (i: int, j: int)
  // pre-conditions-start
  requires n >= 0
  requires k == 1 || k >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures k + i + j >= 2 * n
  // post-conditions-end
{
// impl-start
  i := 0;
  j := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant j == i * (i + 1) / 2
    // invariants-end

  {
    i := i + 1;
    j := j + i;
  }
// impl-end
}
