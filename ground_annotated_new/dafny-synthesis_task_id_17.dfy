method SquarePerimeter(side: int) returns (perimeter: int)
  // pre-conditions-start
  requires side > 0
  // pre-conditions-end
  // post-conditions-start
  ensures perimeter == 4 * side
  // post-conditions-end
{
// impl-start
  perimeter := 4 * side;
// impl-end
}
