function Par(n: int): bool
{
  n % 2 == 0
}
// pure-end

method FazAlgo(a: int, b: int)
    returns (x: int, y: int)
  // pre-conditions-start
  requires a >= b && Par(a - b)
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  x := a;
  y := b;
  while x != y
    // invariants-start

    invariant x >= y
    invariant Par(x - y)
    decreases x - y
    // invariants-end

  {
    x := x - 1;
    y := y + 1;
  }
// impl-end
}
