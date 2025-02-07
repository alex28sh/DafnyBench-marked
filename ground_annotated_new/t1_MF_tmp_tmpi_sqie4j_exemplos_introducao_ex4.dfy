function Fat(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Fat(n - 1)
}
// pure-end

method Fatorial(n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == Fat(n)
  // post-conditions-end
{
// impl-start
  r := 1;
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant r == Fat(i)
    // invariants-end

  {
    i := i + 1;
    r := r * i;
  }
// impl-end
}
