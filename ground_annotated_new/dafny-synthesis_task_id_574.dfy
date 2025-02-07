method CylinderSurfaceArea(radius: real, height: real) returns (area: real)
  // pre-conditions-start
  requires radius > 0.0 && height > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
  // post-conditions-end
{
// impl-start
  area := 2.0 * 3.14159265358979323846 * radius * (radius + height);
// impl-end
}
