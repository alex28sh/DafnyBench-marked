function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}
// pure-end

method CalcPower(n: nat) returns (p: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p == 2 * n
  // post-conditions-end
{
// impl-start
  p := 2 * n;
// impl-end
}

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

    invariant 0 <= i <= n
    invariant p * Power(n - i) == Power(n)
    // invariants-end

  {
    p := CalcPower(p);
    i := i + 1;
  }
// impl-end
}
