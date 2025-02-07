method CubeVolume(size: int) returns (volume: int)
  // pre-conditions-start
  requires size > 0
  // pre-conditions-end
  // post-conditions-start
  ensures volume == size * size * size
  // post-conditions-end
{
// impl-start
  volume := size * size * size;
// impl-end
}
