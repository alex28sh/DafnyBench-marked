method NthOctagonalNumber(n: int) returns (octagonalNumber: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures octagonalNumber == n * (3 * n - 2)
  // post-conditions-end
{
// impl-start
  octagonalNumber := n * (3 * n - 2);
// impl-end
}
