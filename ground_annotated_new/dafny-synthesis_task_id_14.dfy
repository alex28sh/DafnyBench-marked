method TriangularPrismVolume(base: int, height: int, length: int)
    returns (volume: int)
  // pre-conditions-start
  requires base > 0
  requires height > 0
  requires length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures volume == base * height * length / 2
  // post-conditions-end
{
// impl-start
  volume := base * height * length / 2;
// impl-end
}
