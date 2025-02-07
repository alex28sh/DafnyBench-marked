method DegreesToRadians(degrees: real) returns (radians: real)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures radians == degrees * 3.14159265358979323846 / 180.0
  // post-conditions-end
{
// impl-start
  radians := degrees * 3.14159265358979323846 / 180.0;
// impl-end
}
