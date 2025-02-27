method CubeSurfaceArea(size: int) returns (area: int)
  // pre-conditions-start
  requires size > 0
  // pre-conditions-end
  // post-conditions-start
  ensures area == 6 * size * size
  // post-conditions-end
{
// impl-start
  area := 6 * size * size;
// impl-end
}
