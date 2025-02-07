method CylinderLateralSurfaceArea(radius: real, height: real) returns (area: real)
  // pre-conditions-start
  requires radius > 0.0 && height > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures area == 2.0 * (radius * height) * 3.14
  // post-conditions-end
{
// impl-start
  area := 2.0 * (radius * height) * 3.14;
// impl-end
}
