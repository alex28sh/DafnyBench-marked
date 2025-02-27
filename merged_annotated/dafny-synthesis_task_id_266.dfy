method LateralSurfaceArea(size: int) returns (area: int)
  // pre-conditions-start
  requires size > 0
  // pre-conditions-end
  // post-conditions-start
  ensures area == 4 * size * size
  // post-conditions-end
{
// impl-start
  area := 4 * size * size;
// impl-end
}
