method Fact(x: int) returns (y: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  y := 1;
  var z := 0;
  while z != x
    // invariants-start

    invariant 0 <= x - z
    decreases x - z
    // invariants-end

  {
    z := z + 1;
    y := y * z;
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
  var a := Fact(87);
  print a;
// impl-end
}
