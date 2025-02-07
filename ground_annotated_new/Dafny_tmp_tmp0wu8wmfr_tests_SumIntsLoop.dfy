function sumInts(n: int): int
  requires n >= 0
{
  if n == 0 then
    0
  else
    sumInts(n - 1) + n
}
// pure-end

method SumIntsLoop(n: int) returns (s: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures s == sumInts(n)
  ensures s == n * (n + 1) / 2
  // post-conditions-end
{
// impl-start
  s := 0;
  var k := 0;
  while k != n
    // invariants-start

    invariant 0 <= k <= n
    invariant s == sumInts(k)
    invariant s == k * (k + 1) / 2
    decreases n - k
    // invariants-end

  {
    k := k + 1;
    s := s + k;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x := SumIntsLoop(100);
  print x;
// impl-end
}
