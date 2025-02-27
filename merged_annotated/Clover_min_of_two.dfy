method Min(x: int, y: int) returns (z: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x <= y ==> z == x
  ensures x > y ==> z == y
  // post-conditions-end
{
// impl-start
  if x < y {
    return x;
  } else {
    return y;
  }
// impl-end
}
