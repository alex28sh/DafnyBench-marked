method IsLengthOdd(s: string) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> |s| % 2 == 1
  // post-conditions-end
{
// impl-start
  result := |s| % 2 == 1;
// impl-end
}
