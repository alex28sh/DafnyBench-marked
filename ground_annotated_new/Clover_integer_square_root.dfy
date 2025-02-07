method SquareRoot(N: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r * r <= N < (r + 1) * (r + 1)
  // post-conditions-end
{
// impl-start
  r := 0;
  while (r + 1) * (r + 1) <= N
    // invariants-start

    invariant r * r <= N
    // invariants-end

  {
    r := r + 1;
  }
// impl-end
}
