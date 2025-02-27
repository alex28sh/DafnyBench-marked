function R(n: nat): nat
{
  if n == 0 then
    0
  else if R(n - 1) > n then
    R(n - 1) - n
  else
    R(n - 1) + n
}
// pure-end

method calcR(n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == R(n)
  // post-conditions-end
{
// impl-start
  r := 0;
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant r == R(i)
    decreases n - i
    // invariants-end

  {
    i := i + 1;
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
  }
// impl-end
}
