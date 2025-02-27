method Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  // pre-conditions-start
  requires y != 0
  // pre-conditions-end
  // post-conditions-start
  ensures q * y + r == x && 0 <= r < y && 0 <= q
  // post-conditions-end
{
// impl-start
  r := x;
  q := 0;
  while y <= r
    // invariants-start

    invariant q * y + r == x && r >= 0
    decreases r
    // invariants-end

  {
    r := r - y;
    q := q + 1;
  }
// impl-end
}
