method IsEven(n: int) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> n % 2 == 0
  // post-conditions-end
{
// impl-start
  result := n % 2 == 0;
// impl-end
}
