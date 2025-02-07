method Quotient(a: int, b: int) returns (result: int)
  // pre-conditions-start
  requires b != 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == a / b
  // post-conditions-end
{
// impl-start
  result := a / b;
// impl-end
}
