method HasOppositeSign(a: int, b: int) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
  // post-conditions-end
{
// impl-start
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
// impl-end
}
