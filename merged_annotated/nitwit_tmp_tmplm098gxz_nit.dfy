function valid_base(b: nat): bool
{
  b >= 2
}
// pure-end

function nitness(b: nat, n: nat): bool
  requires valid_base(b)
{
  0 <= n < b
}
// pure-end

method nit_increment(b: nat, n: nat)
    returns (sum: nat, carry: nat)
  // pre-conditions-start
  requires valid_base(b)
  requires nitness(b, n)
  // pre-conditions-end
  // post-conditions-start
  ensures nitness(b, sum)
  ensures nitness(b, carry)
  // post-conditions-end
{
// impl-start
  sum := (n + 1) % b;
  carry := (n + 1) / b;
// impl-end
}

function is_max_nit(b: nat, q: nat): bool
{
  q == b - 1
}
// pure-end

method max_nit(b: nat) returns (nmax: nat)
  // pre-conditions-start
  requires valid_base(b)
  // pre-conditions-end
  // post-conditions-start
  ensures nitness(b, nmax)
  ensures is_max_nit(b, nmax)
  // post-conditions-end
{
// impl-start
  nmax := b - 1;
// impl-end
}

method nit_flip(b: nat, n: nat) returns (nf: nat)
  // pre-conditions-start
  requires valid_base(b)
  requires nitness(b, n)
  // pre-conditions-end
  // post-conditions-start
  ensures nitness(b, nf)
  // post-conditions-end
{
// impl-start
  var mn: nat := max_nit(b);
  // assert-start
  assert 0 < n < b ==> n <= b - 1;
  // assert-end

  // assert-start
  assert 0 == n ==> n <= b - 1;
  // assert-end

  // assert-start
  assert n <= b - 1;
  // assert-end

  // assert-start
  assert mn == b - 1;
  // assert-end

  // assert-start
  assert 0 <= n <= mn;
  // assert-end

  nf := mn - n;
// impl-end
}

method nit_add(b: nat, x: nat, y: nat)
    returns (z: nat, carry: nat)
  // pre-conditions-start
  requires valid_base(b)
  requires nitness(b, x)
  requires nitness(b, y)
  // pre-conditions-end
  // post-conditions-start
  ensures nitness(b, z)
  ensures nitness(b, carry)
  ensures carry == 0 || carry == 1
  // post-conditions-end
{
// impl-start
  z := (x + y) % b;
  carry := (x + y) / b;
  // assert-start
  assert x + y < b + b;
  // assert-end

  // assert-start
  assert (x + y) / b < (b + b) / b;
  // assert-end

  // assert-start
  assert (x + y) / b < 2;
  // assert-end

  // assert-start
  assert carry < 2;
  // assert-end

  // assert-start
  assert carry == 0 || carry == 1;
  // assert-end

// impl-end
}

method nit_add_three(b: nat, c: nat, x: nat, y: nat)
    returns (z: nat, carry: nat)
  // pre-conditions-start
  requires valid_base(b)
  requires c == 0 || c == 1
  requires nitness(b, x)
  requires nitness(b, y)
  // pre-conditions-end
  // post-conditions-start
  ensures nitness(b, z)
  ensures nitness(b, carry)
  ensures carry == 0 || carry == 1
  // post-conditions-end
{
// impl-start
  if c == 0 {
    z, carry := nit_add(b, x, y);
  } else {
    z := (x + y + 1) % b;
    carry := (x + y + 1) / b;
    // assert-start
    assert 0 <= b - 1;
    // assert-end

    // assert-start
    assert 0 <= x < b;
    // assert-end

    // assert-start
    assert 0 == x || 0 < x;
    // assert-end

    // assert-start
    assert 0 < x ==> x <= b - 1;
    // assert-end

    // assert-start
    assert 0 <= x <= b - 1;
    // assert-end

    // assert-start
    assert 0 <= y < b;
    // assert-end

    // assert-start
    assert 0 == y || 0 < y;
    // assert-end

    // assert-start
    assert 0 <= b - 1;
    // assert-end

    // assert-start
    assert 0 < y ==> y <= b - 1;
    // assert-end

    // assert-start
    assert 0 <= y <= b - 1;
    // assert-end

    // assert-start
    assert x + y <= b - 1 + (b - 1);
    // assert-end

    // assert-start
    assert x + y <= 2 * b - 2;
    // assert-end

    // assert-start
    assert x + y + 1 <= 2 * b - 2 + 1;
    // assert-end

    // assert-start
    assert x + y + 1 <= 2 * b - 1;
    // assert-end

    // assert-start
    assert 2 * b - 1 < 2 * b;
    // assert-end

    // assert-start
    assert x + y + 1 < 2 * b;
    // assert-end

    // assert-start
    assert (x + y + 1) / b < 2;
    // assert-end

    // assert-start
    assert (x + y + 1) / b == 0 || (x + y + 1) / b == 1;
    // assert-end

  }
// impl-end
}

function bibble(b: nat, a: seq<nat>): bool
{
  valid_base(b) &&
  |a| == 4 &&
  forall n :: 
    n in a ==>
      nitness(b, n)
}
// pure-end

method bibble_add(b: nat, p: seq<nat>, q: seq<nat>)
    returns (r: seq<nat>)
  // pre-conditions-start
  requires valid_base(b)
  requires bibble(b, p)
  requires bibble(b, q)
  // pre-conditions-end
  // post-conditions-start
  ensures bibble(b, r)
  // post-conditions-end
{
// impl-start
  var z3, c3 := nit_add(b, p[3], q[3]);
  var z2, c2 := nit_add_three(b, c3, p[2], q[2]);
  var z1, c1 := nit_add_three(b, c2, p[1], q[1]);
  var z0, c0 := nit_add_three(b, c1, p[0], q[0]);
  r := [z0, z1, z2, z3];
// impl-end
}

method bibble_increment(b: nat, p: seq<nat>) returns (r: seq<nat>)
  // pre-conditions-start
  requires valid_base(b)
  requires bibble(b, p)
  // pre-conditions-end
  // post-conditions-start
  ensures bibble(b, r)
  // post-conditions-end
{
// impl-start
  var q: seq<nat> := [0, 0, 0, 1];
  // assert-start
  assert bibble(b, q);
  // assert-end

  r := bibble_add(b, p, q);
// impl-end
}

method bibble_flip(b: nat, p: seq<nat>) returns (fp: seq<nat>)
  // pre-conditions-start
  requires valid_base(b)
  requires bibble(b, p)
  // pre-conditions-end
  // post-conditions-start
  ensures bibble(b, fp)
  // post-conditions-end
{
// impl-start
  var n0 := nit_flip(b, p[0]);
  var n1 := nit_flip(b, p[1]);
  var n2 := nit_flip(b, p[2]);
  var n3 := nit_flip(b, p[3]);
  fp := [n0, n1, n2, n3];
// impl-end
}

method n_complement(b: nat, p: seq<nat>) returns (com: seq<nat>)
  // pre-conditions-start
  requires valid_base(b)
  requires bibble(b, p)
  // pre-conditions-end
  // post-conditions-start
  ensures bibble(b, com)
  // post-conditions-end
{
// impl-start
  var fp := bibble_flip(b, p);
  var fpi := bibble_increment(b, fp);
  com := fpi;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var b := 3;
  var bibble1 := [2, 1, 0, 2];
  var complement := n_complement(b, bibble1);
  var bibble_sum := bibble_add(b, bibble1, complement);
  print bibble1, " + ", complement, " = ", bibble_sum, " (should be [0, 0, 0, 0])\n";
// impl-end
}
