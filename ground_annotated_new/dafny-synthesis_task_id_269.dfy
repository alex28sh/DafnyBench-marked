method AsciiValue(c: char) returns (ascii: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures ascii == c as int
  // post-conditions-end
{
// impl-start
  ascii := c as int;
// impl-end
}
