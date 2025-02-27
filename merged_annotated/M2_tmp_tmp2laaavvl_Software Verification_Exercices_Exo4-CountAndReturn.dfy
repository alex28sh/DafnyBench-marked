method CountToAndReturnN(n: int) returns (r: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == n
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    // invariants-end

  {
    i := i + 1;
  }
  r := i;
// impl-end
}
