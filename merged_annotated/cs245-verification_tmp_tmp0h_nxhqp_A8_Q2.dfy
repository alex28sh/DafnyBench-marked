method A8Q1(x: int, y: int, z: int)
    returns (m: int)
  // pre-conditions-start
  requires true
  // pre-conditions-end
  // post-conditions-start
  ensures m <= x && m <= y && m <= z
  // post-conditions-end
{
// impl-start
  if z < y {
    if z < x {
      m := z;
    } else {
      m := x;
    }
  } else {
    m := y;
    if x < y {
      m := x;
    }
  }
// impl-end
}
