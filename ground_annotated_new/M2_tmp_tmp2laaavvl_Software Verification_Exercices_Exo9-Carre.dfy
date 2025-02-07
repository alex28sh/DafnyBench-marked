method Carre(a: nat) returns (c: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c == a * a
  // post-conditions-end
{
// impl-start
  var i := 0;
  c := 0;
  while i != a
    // invariants-start

    invariant 0 <= i <= a
    invariant c == i * i
    decreases a - i
    // invariants-end

  {
    c := c + 2 * i + 1;
    i := i + 1;
  }
// impl-end
}
