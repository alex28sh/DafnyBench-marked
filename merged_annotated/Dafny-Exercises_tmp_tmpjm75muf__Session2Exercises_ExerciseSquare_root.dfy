method mroot1(n: int) returns (r: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
  // post-conditions-end
{
// impl-start
  r := 0;
  while (r + 1) * (r + 1) <= n
    // invariants-start

    invariant r >= 0 && r * r <= n
    decreases n - r * r
    // invariants-end

  {
    r := r + 1;
  }
// impl-end
}

method mroot2(n: int) returns (r: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
  // post-conditions-end
{
// impl-start
  r := n;
  while n < r * r
    // invariants-start

    invariant 0 <= r <= n && n < (r + 1) * (r + 1)
    invariant r * r <= n ==> n < (r + 1) * (r + 1)
    decreases r
    // invariants-end

  {
    r := r - 1;
  }
// impl-end
}

method mroot3(n: int) returns (r: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
  // post-conditions-end
{
// impl-start
  var y: int;
  var h: int;
  r := 0;
  y := n + 1;
  while y != r + 1
    // invariants-start

    invariant r >= 0 && r * r <= n < y * y && y >= r + 1
    decreases y - r
    // invariants-end

  {
    h := (r + y) / 2;
    if h * h <= n {
      r := h;
    } else {
      y := h;
    }
  }
// impl-end
}
