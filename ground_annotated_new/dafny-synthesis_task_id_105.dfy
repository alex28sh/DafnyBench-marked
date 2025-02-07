function countTo(a: array<bool>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
  decreases n
{
  if n == 0 then
    0
  else
    countTo(a, n - 1) + if a[n - 1] then 1 else 0
}
// pure-end

method CountTrue(a: array<bool>) returns (result: int)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures result == countTo(a, a.Length)
  // post-conditions-end
{
// impl-start
  result := 0;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result == countTo(a, i)
    // invariants-end

  {
    if a[i] {
      result := result + 1;
    }
  }
// impl-end
}
