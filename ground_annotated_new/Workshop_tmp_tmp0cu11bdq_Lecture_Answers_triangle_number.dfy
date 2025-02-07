method TriangleNumber(N: int) returns (t: int)
  // pre-conditions-start
  requires N >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures t == N * (N + 1) / 2
  // post-conditions-end
{
// impl-start
  t := 0;
  var n := 0;
  while n < N
    // invariants-start

    invariant 0 <= n <= N
    invariant t == n * (n + 1) / 2
    decreases N - n
    // invariants-end

  {
    n := n + 1;
    t := t + n;
  }
// impl-end
}
