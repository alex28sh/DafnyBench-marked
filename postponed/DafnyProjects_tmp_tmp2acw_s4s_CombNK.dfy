function comb(n: nat, k: nat): nat
  requires 0 <= k <= n
{
  if k == 0 || k == n then
    1
  else
    comb(n - 1, k) + comb(n - 1, k - 1)
} by method {
  var maxj := n - k;
  var c := new nat[1 + maxj];
  forall i | 0 <= i <= maxj {
    c[i] := 1;
  }
  var i := 1;
  while i <= k
    invariant 1 <= i <= k + 1
    invariant forall j :: 0 <= j <= maxj ==> c[j] == comb(j + i - 1, i - 1)
  {
    var j := 1;
    while j <= maxj
      invariant 1 <= j <= maxj + 1
      invariant forall j' :: 0 <= j' < j ==> c[j'] == comb(j' + i, i)
      invariant forall j' :: j <= j' <= maxj ==> c[j'] == comb(j' + i - 1, i - 1)
    {
      c[j] := c[j] + c[j - 1];
      j := j + 1;
    }
    i := i + 1;
  }
  return c[maxj];
}
// pure-end

lemma combProps(n: nat, k: nat)
  // pre-conditions-start
  requires 0 <= k <= n
  // pre-conditions-end
  // post-conditions-start
  ensures comb(n, k) == comb(n, n - k)
  // post-conditions-end
{
// impl-start
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert comb(5, 2) == 10;
  // assert-end

  // assert-start
  assert comb(5, 0) == 1;
  // assert-end

  // assert-start
  assert comb(5, 5) == 1;
  // assert-end

  // assert-start
  assert comb(5, 2) == 10;
  // assert-end

  var res1 := comb(40, 10);
  print "combDyn(40, 10) = ", res1, "\n";
// impl-end
}

method testComb()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert comb(6, 2) == 15;
  // assert-end

  // assert-start
  assert comb(6, 3) == 20;
  // assert-end

  // assert-start
  assert comb(6, 4) == 15;
  // assert-end

  // assert-start
  assert comb(6, 6) == 1;
  // assert-end

// impl-end
}
