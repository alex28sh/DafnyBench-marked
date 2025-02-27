method SquarePyramidSurfaceArea(baseEdge: int, height: int) returns (area: int)
  // pre-conditions-start
  requires baseEdge > 0
  requires height > 0
  // pre-conditions-end
  // post-conditions-start
  ensures area == baseEdge * baseEdge + 2 * baseEdge * height
  // post-conditions-end
{
// impl-start
  area := baseEdge * baseEdge + 2 * baseEdge * height;
// impl-end
}
