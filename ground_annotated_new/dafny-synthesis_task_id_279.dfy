method NthDecagonalNumber(n: int) returns (decagonal: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures decagonal == 4 * n * n - 3 * n
  // post-conditions-end
{
// impl-start
  decagonal := 4 * n * n - 3 * n;
// impl-end
}
