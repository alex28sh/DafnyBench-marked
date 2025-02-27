function has_count(v: int, a: array<int>, n: int): int
  requires n >= 0 && n <= a.Length
  reads a
{
  if n == 0 then
    0
  else
    if a[n - 1] == v then has_count(v, a, n - 1) + 1 else has_count(v, a, n - 1)
}
// pure-end

method count(v: int, a: array<int>, n: int)
    returns (r: int)
  // pre-conditions-start
  requires n >= 0 && n <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures has_count(v, a, n) == r
  // post-conditions-end
{
// impl-start
  var i: int;
  i := 0;
  r := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant r == has_count(v, a, i)
    // invariants-end

  {
    if a[i] == v {
      r := r + 1;
    }
    i := i + 1;
  }
  return r;
// impl-end
}
