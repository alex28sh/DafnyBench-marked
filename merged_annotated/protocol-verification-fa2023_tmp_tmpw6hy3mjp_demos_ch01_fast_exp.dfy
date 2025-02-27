function exp(b: nat, n: nat): nat
{
  if n == 0 then
    1
  else
    b * exp(b, n - 1)
}
// pure-end

lemma exp_sum(b: nat, n1: nat, n2: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
  // post-conditions-end
{
// impl-start
  if n1 == 0 {
    return;
  }
  exp_sum(b, n1 - 1, n2);
// impl-end
}

lemma exp_sum_auto(b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
  // post-conditions-end
{
// impl-start
  forall n1: nat, n2: nat | true
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
  {
    exp_sum(b, n1, n2);
  }
// impl-end
}

function bits(n: nat): seq<bool>
  decreases n
{
  if n == 0 then
    []
  else
    [if n % 2 == 0 then false else true] + bits(n / 2)
}
// pure-end

function from_bits(s: seq<bool>): nat
{
  if s == [] then
    0
  else
    (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}
// pure-end

lemma bits_from_bits(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures from_bits(bits(n)) == n
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma from_bits_append(s: seq<bool>, b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * if b then 1 else 0
  // post-conditions-end
{
// impl-start
  if s == [] {
    return;
  }
  assert s == [s[0]] + s[1..];
  from_bits_append(s[1..], b);
  assert from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s| - 1) * if b then 1 else 0;
  exp_sum(2, |s| - 1, 1);
  assert (s + [b])[1..] == s[1..] + [b];
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
// impl-end
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == exp(b, n)
  // post-conditions-end
{
// impl-start
  var a := 1;
  var c := b;
  var n := n;
  ghost var n0 := n;
  ghost var i: nat := 0;
  // assert-start
  bits_from_bits(n);
  // assert-end

  while n > 0
    // invariants-start

    invariant n <= n0
    invariant i <= |bits(n0)|
    invariant c == exp(b, exp(2, i))
    invariant bits(n) == bits(n0)[i..]
    invariant n == from_bits(bits(n0)[i..])
    invariant a == exp(b, from_bits(bits(n0)[..i]))
    decreases n
    // invariants-end

  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      // assert-start
      assert bits(n)[0] == true;
      // assert-end

      a := a * c;
      // assert-start
      exp_sum(b, n0 - n, i);
      // assert-end

      n := n / 2;
      // assert-start
      assert a == exp(b, from_bits(bits(n0)[..i]) + exp(2, i)) by {
        exp_sum_auto(b);
      }
      // assert-end

      // assert-start
      assert bits(n0)[..i + 1] == bits(n0)[..i] + [bits(n0)[i]];
      // assert-end

      // assert-start
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      // assert-end

      // assert-start
      assert a == exp(b, from_bits(bits(n0)[..i + 1]));
      // assert-end

    } else {
      // assert-start
      assert bits(n)[0] == false;
      // assert-end

      n := n / 2;
      // assert-start
      assert bits(n0)[..i + 1] == bits(n0)[..i] + [bits(n0)[i]];
      // assert-end

      // assert-start
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      // assert-end

      // assert-start
      assert a == exp(b, from_bits(bits(n0)[..i + 1]));
      // assert-end

    }
    // assert-start
    assert n == n_loop_top / 2;
    // assert-end

    c := c * c;
    // assert-start
    assert c == exp(b, exp(2, i + 1)) by {
      exp_sum_auto(b);
    }
    // assert-end

    i := i + 1;
  }
  // assert-start
  assert bits(n0)[..i] == bits(n0);
  // assert-end

  return a;
// impl-end
}
