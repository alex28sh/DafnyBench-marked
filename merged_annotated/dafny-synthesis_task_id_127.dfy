method Multiply(a: int, b: int) returns (result: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result == a * b
  // post-conditions-end
{
// impl-start
  result := a * b;
// impl-end
}
