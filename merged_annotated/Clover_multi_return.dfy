method MultipleReturns(x: int, y: int)
    returns (more: int, less: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures more == x + y
  ensures less == x - y
  // post-conditions-end
{
// impl-start
  more := x + y;
  less := x - y;
// impl-end
}
