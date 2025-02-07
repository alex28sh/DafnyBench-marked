method ClosestSmaller(n: int) returns (m: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures m + 1 == n
  // post-conditions-end
{
// impl-start
  m := n - 1;
// impl-end
}
