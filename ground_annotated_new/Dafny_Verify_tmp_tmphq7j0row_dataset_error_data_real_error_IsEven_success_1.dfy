function even(n: int): bool
  requires n >= 0
{
  if n == 0 then
    true
  else
    !even(n - 1)
}
// pure-end

method is_even(n: int) returns (r: bool)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r <==> even(n)
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  r := true;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant r <==> even(i)
    // invariants-end

  {
    r := !r;
    i := i + 1;
  }
// impl-end
}
