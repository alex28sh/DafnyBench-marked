method LastDigit(n: int) returns (d: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= d < 10
  ensures n % 10 == d
  // post-conditions-end
{
// impl-start
  d := n % 10;
// impl-end
}
