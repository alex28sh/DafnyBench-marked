function IsDigit(c: char): bool
{
  48 <= c as int <= 57
}
// pure-end

method CountDigits(s: string) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
  // post-conditions-end
{
// impl-start
  var digits := set i: int | 0 <= i < |s| && IsDigit(s[i]);
  count := |digits|;
// impl-end
}
