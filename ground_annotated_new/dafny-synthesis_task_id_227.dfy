method MinOfThree(a: int, b: int, c: int)
    returns (min: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures min <= a && min <= b && min <= c
  ensures min == a || min == b || min == c
  // post-conditions-end
{
// impl-start
  if a <= b && a <= c {
    min := a;
  } else if b <= a && b <= c {
    min := b;
  } else {
    min := c;
  }
// impl-end
}
