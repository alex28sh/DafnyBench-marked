method ConeVolume(radius: real, height: real) returns (volume: real)
  // pre-conditions-start
  requires radius > 0.0 && height > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures volume == 1.0 / 3.0 * 3.14159265358979323846 * radius * radius * height
  // post-conditions-end
{
// impl-start
  volume := 1.0 / 3.0 * 3.14159265358979323846 * radius * radius * height;
// impl-end
}
