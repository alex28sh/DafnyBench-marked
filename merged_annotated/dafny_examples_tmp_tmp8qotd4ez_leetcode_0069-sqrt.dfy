function sqrt(x: int, r: int): bool
{
  r * r <= x &&
  (r + 1) * (r + 1) > x
}
// pure-end

lemma uniqueSqrt(x: int, r1: int, r2: int)
  // pre-conditions-start
  requires x >= 0 && r1 >= 0 && r2 >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
  // post-conditions-end
{
// impl-start
// impl-end
}

method mySqrt(x: int) returns (res: int)
  // pre-conditions-start
  requires 0 <= x
  // pre-conditions-end
  // post-conditions-start
  ensures sqrt(x, res)
  // post-conditions-end
{
// impl-start
  var l, r := 0, x;
  while l <= r
    // invariants-start

    invariant l >= 0
    invariant r >= 0
    invariant l * l <= x
    invariant (r + 1) * (r + 1) > x
    decreases r - l
    // invariants-end

  {
    var mid := (l + r) / 2;
    if mid * mid <= x && (mid + 1) * (mid + 1) > x {
      return mid;
    } else if mid * mid <= x {
      l := mid + 1;
    } else {
      r := mid - 1;
    }
  }
// impl-end
}
