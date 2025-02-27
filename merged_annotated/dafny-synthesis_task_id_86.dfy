method CenteredHexagonalNumber(n: nat) returns (result: nat)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == 3 * n * (n - 1) + 1
  // post-conditions-end
{
// impl-start
  result := 3 * n * (n - 1) + 1;
// impl-end
}
