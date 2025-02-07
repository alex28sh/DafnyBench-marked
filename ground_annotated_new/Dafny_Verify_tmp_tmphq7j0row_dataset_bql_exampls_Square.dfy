method square(n: int) returns (r: int)
  // pre-conditions-start
  requires 0 <= n
  // pre-conditions-end
  // post-conditions-start
  ensures r == n * n
  // post-conditions-end
{
// impl-start
  var x: int;
  var i: int;
  r := 0;
  i := 0;
  x := 1;
  while i < n
    // invariants-start

    invariant i <= n
    invariant r == i * i
    invariant x == 2 * i + 1
    // invariants-end

  {
    r := r + x;
    x := x + 2;
    i := i + 1;
  }
// impl-end
}
