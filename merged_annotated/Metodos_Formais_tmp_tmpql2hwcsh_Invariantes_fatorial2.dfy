function Fat(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Fat(n - 1)
}
// pure-end

method Fatorial(n: nat) returns (f: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f == Fat(n)
  // post-conditions-end
{
// impl-start
  f := 1;
  var i := 1;
  while i <= n
    // invariants-start

    invariant 1 <= i <= n + 1
    invariant f == Fat(i - 1)
    decreases n - i
    // invariants-end

  {
    f := f * i;
    i := i + 1;
  }
  return f;
// impl-end
}
