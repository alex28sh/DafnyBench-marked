method Compare<T(==)>(a: T, b: T) returns (eq: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == b ==> eq == true
  ensures a != b ==> eq == false
  // post-conditions-end
{
// impl-start
  if a == b {
    eq := true;
  } else {
    eq := false;
  }
// impl-end
}
