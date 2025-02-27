method Cube(n: nat) returns (c: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c == n * n * n
  // post-conditions-end
{
// impl-start
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i != n
    // invariants-start

    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
    // invariants-end

  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
// impl-end
}
