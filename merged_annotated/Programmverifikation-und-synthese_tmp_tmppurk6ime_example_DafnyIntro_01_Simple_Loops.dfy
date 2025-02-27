method Gauss(n: int) returns (sum: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == n * (n + 1) / 2
  // post-conditions-end
{
// impl-start
  sum := 0;
  var i := 0;
  while i < n
    // invariants-start

    invariant sum == i * (i + 1) / 2
    invariant i <= n
    // invariants-end

  {
    i := i + 1;
    sum := sum + i;
  }
// impl-end
}

method sumOdds(n: nat) returns (sum: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sum == n * n
  // post-conditions-end
{
// impl-start
  sum := 0;
  var i := 0;
  while i < n
    // invariants-start

    invariant sum == i * i
    invariant i <= n
    // invariants-end

  {
    sum := sum + 2 * i + 1;
    i := i + 1;
  }
// impl-end
}
