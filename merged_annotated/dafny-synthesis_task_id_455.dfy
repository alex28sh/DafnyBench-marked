method MonthHas31Days(month: int) returns (result: bool)
  // pre-conditions-start
  requires 1 <= month <= 12
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
  // post-conditions-end
{
// impl-start
  result := month in {1, 3, 5, 7, 8, 10, 12};
// impl-end
}
