function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then
    1
  else
    b * Expt(b, n - 1)
}
// pure-end

method expt(b: int, n: nat) returns (res: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == Expt(b, n)
  // post-conditions-end
{
// impl-start
  var i := 1;
  res := 1;
  while i < n + 1
    // invariants-start

    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
    // invariants-end

  {
    res := res * b;
    i := i + 1;
  }
// impl-end
}

lemma {:induction a} distributive(x: int, a: nat, b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
  // post-conditions-end
