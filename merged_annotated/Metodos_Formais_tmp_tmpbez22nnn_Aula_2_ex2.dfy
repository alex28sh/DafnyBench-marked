function Potencia(x: nat, y: nat): nat
{
  if y == 0 then
    1
  else
    x * Potencia(x, y - 1)
}
// pure-end

method Pot(x: nat, y: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == Potencia(x, y)
  // post-conditions-end
{
// impl-start
  var b := x;
  var e := y;
  r := 1;
  while e > 0
    // invariants-start

    invariant Potencia(b, e) * r == Potencia(x, y)
    // invariants-end

  {
    r := b * r;
    e := e - 1;
  }
  return r;
// impl-end
}
