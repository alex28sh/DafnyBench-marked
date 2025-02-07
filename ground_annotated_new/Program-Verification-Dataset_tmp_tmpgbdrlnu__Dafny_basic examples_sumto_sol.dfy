function sum_up_to(n: nat): nat
{
  if n == 0 then
    0
  else
    sum_up_to(n - 1) + 1
}
// pure-end

method SumUpTo(n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == sum_up_to(n)
  // post-conditions-end
{
// impl-start
  var i := 0;
  r := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant r == sum_up_to(i)
    // invariants-end

  {
    r := r + 1;
    i := i + 1;
  }
// impl-end
}

function total(a: seq<nat>): nat
{
  if |a| == 0 then
    0
  else
    total(a[0 .. |a| - 1]) + a[|a| - 1]
}
// pure-end

lemma total_lemma(a: seq<nat>, i: nat)
  // pre-conditions-start
  requires |a| > 0
  requires 0 <= i < |a|
  // pre-conditions-end
  // post-conditions-start
  ensures total(a[0 .. i]) + a[i] == total(a[0 .. i + 1])
  // post-conditions-end
{
// impl-start
  ghost var b := a[0 .. i + 1];
  calc {
    total(a[0 .. i + 1]);
    total(b);
    total(b[0 .. |b| - 1]) + b[|b| - 1];
    total(b[0 .. |b| - 1]) + a[i];
    {
      assert b[0 .. |b| - 1] == a[0 .. i];
    }
    total(a[0 .. i]) + a[i];
  }
// impl-end
}

method Total(a: seq<nat>) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == total(a[0 .. |a|])
  // post-conditions-end
{
// impl-start
  var i := 0;
  r := 0;
  while i < |a|
    // invariants-start

    invariant 0 <= i <= |a|
    invariant r == total(a[0 .. i])
    // invariants-end

  {
    // assert-start
    total_lemma(a, i);
    // assert-end

    r := r + a[i];
    i := i + 1;
  }
// impl-end
}
