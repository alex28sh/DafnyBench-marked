method main(n: int, k: int) returns (k_out: int)
  // pre-conditions-start
  requires n > 0
  requires k > n
  // pre-conditions-end
  // post-conditions-start
  ensures k_out >= 0
  // post-conditions-end
{
// impl-start
  k_out := k;
  var j: int := 0;
  while j < n
    // invariants-start

    invariant 0 <= j <= n
    invariant k_out == k - j
    // invariants-end

  {
    j := j + 1;
    k_out := k_out - 1;
  }
// impl-end
}
