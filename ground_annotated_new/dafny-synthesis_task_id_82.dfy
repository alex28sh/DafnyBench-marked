method SphereVolume(radius: real) returns (volume: real)
  // pre-conditions-start
  requires radius > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures volume == 4.0 / 3.0 * 3.1415926535 * radius * radius * radius
  // post-conditions-end
{
// impl-start
  volume := 4.0 / 3.0 * 3.1415926535 * radius * radius * radius;
// impl-end
}
