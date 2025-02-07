method CircleCircumference(radius: real) returns (circumference: real)
  // pre-conditions-start
  requires radius > 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures circumference == 2.0 * 3.14159265358979323846 * radius
  // post-conditions-end
{
// impl-start
  circumference := 2.0 * 3.14159265358979323846 * radius;
// impl-end
}
