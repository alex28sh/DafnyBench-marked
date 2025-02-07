function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}
// pure-end

method ComputePower(n: nat) returns (p: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == Power(n)
  // post-conditions-end
{
// impl-start
  p := 1;
  var i := 0;
  while i != n
    // invariants-start

    invariant 0 <= i <= n && p == Power(i)
    // invariants-end

  {
    i := i + 1;
    p := p * 2;
  }
// impl-end
}
