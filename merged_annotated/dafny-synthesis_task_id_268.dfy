method StarNumber(n: int) returns (star: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures star == 6 * n * (n - 1) + 1
  // post-conditions-end
{
// impl-start
  star := 6 * n * (n - 1) + 1;
// impl-end
}
