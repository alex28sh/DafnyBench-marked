method SphereSurfaceArea(radius: real) returns (area: real)
  // pre-conditions-start
  requires radius > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures area == 4.0 * 3.14159265358979323846 * radius * radius
  // post-conditions-end
{
// impl-start
  area := 4.0 * 3.14159265358979323846 * radius * radius;
// impl-end
}
