method SumOfCommonDivisors(a: int, b: int) returns (sum: int)
  // pre-conditions-start
  requires a > 0 && b > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum >= 0
  ensures forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d
  // post-conditions-end
{
// impl-start
  sum := 0;
  var i := 1;
  while i <= a && i <= b
    // invariants-start

    invariant 1 <= i <= a + 1 && 1 <= i <= b + 1
    invariant sum >= 0
    invariant forall d :: 1 <= d < i && a % d == 0 && b % d == 0 ==> sum >= d
    // invariants-end

  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
// impl-end
}
