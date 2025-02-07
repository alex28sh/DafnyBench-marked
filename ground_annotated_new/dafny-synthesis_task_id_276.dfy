method CylinderVolume(radius: real, height: real) returns (volume: real)
  // pre-conditions-start
  requires radius > 0.0
  requires height > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures volume == 3.14159265359 * radius * radius * height
  // post-conditions-end
{
// impl-start
  volume := 3.14159265359 * radius * radius * height;
// impl-end
}
