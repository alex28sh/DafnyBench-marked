method div_ent_it(a: int, b: int)
    returns (c: int, r: int)
  // pre-conditions-start
  requires a >= 0 && b > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a == b * c + r && 0 <= r < b
  // post-conditions-end
{
// impl-start
  c := 0;
  r := a;
  while r >= b
    // invariants-start

    invariant a == b * c + r && r >= 0 && b > 0
    decreases r
    // invariants-end

  {
    c := c + 1;
    r := r - b;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var c, r := div_ent_it(6, 2);
  print "Cociente: ", c, ", Resto: ", r;
// impl-end
}
