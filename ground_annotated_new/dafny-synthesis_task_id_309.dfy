method Max(a: int, b: int) returns (maxValue: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures maxValue == a || maxValue == b
  ensures maxValue >= a && maxValue >= b
  // post-conditions-end
{
// impl-start
  if a >= b {
    maxValue := a;
  } else {
    maxValue := b;
  }
// impl-end
}
