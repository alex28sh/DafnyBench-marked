method AreaOfLargestTriangleInSemicircle(radius: int) returns (area: int)
  // pre-conditions-start
  requires radius > 0
  // pre-conditions-end
  // post-conditions-start
  ensures area == radius * radius
  // post-conditions-end
{
// impl-start
  area := radius * radius;
// impl-end
}
