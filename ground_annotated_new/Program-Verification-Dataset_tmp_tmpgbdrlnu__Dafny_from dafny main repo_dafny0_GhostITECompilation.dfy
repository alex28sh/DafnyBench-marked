function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1)
  else
    F(x - 1, 60) + 13
}
// pure-end

lemma AboutF(x: nat, y: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures F(x, y) == 13 * x
  // post-conditions-end
{
// impl-start
// impl-end
}

function G(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    var z := x + x;
    var a, b, c := 100, if x < z then G(x, y - 1) else G(x, y - 1), 200;
    assert a + b + c == G(x, y - 1) + 300;
    b
  else
    G(x - 1, 60) + 13
}
// pure-end

function H(x: int, ghost y: nat): int
{
  if y == 0 then
    x
  else
    H(x, y - 1)
}
// pure-end

function J(x: int): int
{
  if true then
    x
  else
    J(x)
}
// pure-end

function {:verify false} K(x: int, ghost y: nat): int
{
  K(x, y - 1)
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  print F(5, 3), "\n";
  print G(5, 3), "\n";
  print H(65, 3), "\n";
  print J(65), "\n";
// impl-end
}
