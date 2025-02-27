method ComputeIsEven(x: int) returns (is_even: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (x % 2 == 0) == is_even
  // post-conditions-end
{
// impl-start
  is_even := false;
  if x % 2 == 0 {
    is_even := true;
  }
// impl-end
}
