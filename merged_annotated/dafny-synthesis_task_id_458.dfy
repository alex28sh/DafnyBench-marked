method RectangleArea(length: int, width: int) returns (area: int)
  // pre-conditions-start
  requires length > 0
  requires width > 0
  // pre-conditions-end
  // post-conditions-start
  ensures area == length * width
  // post-conditions-end
{
// impl-start
  area := length * width;
// impl-end
}
