function IsUpperCase(c: char): bool
{
  65 <= c as int <= 90
}
// pure-end

method CountUppercase(s: string) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
  // post-conditions-end
{
// impl-start
  var uppercase := set i: int | 0 <= i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
// impl-end
}
