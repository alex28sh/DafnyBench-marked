method DogYears(humanYears: int) returns (dogYears: int)
  // pre-conditions-start
  requires humanYears >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures dogYears == 7 * humanYears
  // post-conditions-end
{
// impl-start
  dogYears := 7 * humanYears;
// impl-end
}
