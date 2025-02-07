method TetrahedralNumber(n: int) returns (t: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures t == n * (n + 1) * (n + 2) / 6
  // post-conditions-end
{
// impl-start
  t := n * (n + 1) * (n + 2) / 6;
// impl-end
}
