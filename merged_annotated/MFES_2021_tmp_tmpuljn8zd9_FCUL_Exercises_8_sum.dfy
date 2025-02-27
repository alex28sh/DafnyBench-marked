function calcSum(n: nat): nat
{
  n * (n - 1) / 2
}
// pure-end

method sum(n: nat) returns (s: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == calcSum(n + 1)
  // post-conditions-end
{
// impl-start
  s := 0;
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant s == calcSum(i + 1)
    decreases n - i
    // invariants-end

  {
    i := i + 1;
    s := s + i;
  }
// impl-end
}
