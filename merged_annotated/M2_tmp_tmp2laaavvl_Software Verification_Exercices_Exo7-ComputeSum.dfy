function Sum(n: nat): nat
{
  if n == 0 then
    0
  else
    n + Sum(n - 1)
}
// pure-end

method ComputeSum(n: nat) returns (s: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == Sum(n)
  // post-conditions-end
{
// impl-start
  s := 0;
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant s == Sum(i)
    // invariants-end

  {
    s := s + i + 1;
    i := i + 1;
  }
// impl-end
}
