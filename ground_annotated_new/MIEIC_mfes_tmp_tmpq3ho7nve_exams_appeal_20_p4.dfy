function F(n: nat): nat
{
  if n <= 2 then
    n
  else
    F(n - 1) + F(n - 3)
}
// pure-end

method calcF(n: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == F(n)
  // post-conditions-end
{
// impl-start
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant a == F(i) && b == F(i + 1) && c == F(i + 2)
    decreases n - i
    // invariants-end

  {
    a, b, c := b, c, a + c;
    i := i + 1;
  }
  res := a;
// impl-end
}
