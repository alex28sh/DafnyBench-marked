method NthNonagonalNumber(n: int) returns (number: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures number == n * (7 * n - 5) / 2
  // post-conditions-end
{
// impl-start
  number := n * (7 * n - 5) / 2;
// impl-end
}
