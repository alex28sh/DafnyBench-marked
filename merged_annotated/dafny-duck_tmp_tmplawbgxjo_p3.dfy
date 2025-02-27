method max(x: array<nat>) returns (y: nat)
  // pre-conditions-start
  requires x.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
  ensures y in x[..]
  // post-conditions-end
{
// impl-start
  y := x[0];
  var i := 0;
  while i < x.Length
    // invariants-start

    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> y >= x[j]
    invariant y in x[..]
    // invariants-end

  {
    if y <= x[i] {
      y := x[i];
    }
    i := i + 1;
  }
  // assert-start
  assert y in x[..];
  // assert-end

// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new nat[6] [5, 1, 3, 6, 12, 3];
  var c := max(a);
  // assert-start
  assert c == 12;
  // assert-end

// impl-end
}
