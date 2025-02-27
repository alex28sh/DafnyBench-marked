method IsMonthWith30Days(month: int) returns (result: bool)
  // pre-conditions-start
  requires 1 <= month <= 12
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
  // post-conditions-end
{
// impl-start
  result := month == 4 || month == 6 || month == 9 || month == 11;
// impl-end
}
