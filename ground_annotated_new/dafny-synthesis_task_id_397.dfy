method MedianOfThree(a: int, b: int, c: int)
    returns (median: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures median == a || median == b || median == c
  ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
  // post-conditions-end
{
// impl-start
  if (a <= b && b <= c) || (c <= b && b <= a) {
    median := b;
  } else if (b <= a && a <= c) || (c <= a && a <= b) {
    median := a;
  } else {
    median := c;
  }
// impl-end
}
