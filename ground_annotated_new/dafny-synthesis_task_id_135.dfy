method NthHexagonalNumber(n: int) returns (hexNum: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures hexNum == n * (2 * n - 1)
  // post-conditions-end
{
// impl-start
  hexNum := n * (2 * n - 1);
// impl-end
}
