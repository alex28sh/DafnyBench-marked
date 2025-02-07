method Min(a: int, b: int) returns (minValue: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures minValue == a || minValue == b
  ensures minValue <= a && minValue <= b
  // post-conditions-end
{
// impl-start
  if a <= b {
    minValue := a;
  } else {
    minValue := b;
  }
// impl-end
}
