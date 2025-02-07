method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var q := [7, -2, 3, -2];
  var p, c := ProdAndCount(q, -2);
  print "The product of all positive elements in [7,-2,3,-2] is ";
  print p;
  // assert-start
  assert p == RecursivePositiveProduct(q) == 21;
  // assert-end

  print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
  print c;
  // assert-start
  assert c == RecursiveCount(-2, q) == 2 by {
    calc {
      RecursiveCount(-2, q);
    ==
      {
        assert q[3] == -2;
        AppendOne(q, 3);
      }
      1 + RecursiveCount(-2, q[..3]);
    ==
      {
        assert q[2] != -2;
        AppendOne(q, 2);
      }
      1 + RecursiveCount(-2, q[..2]);
    ==
      {
        assert q[1] == -2;
        AppendOne(q, 1);
      }
      1 + 1 + RecursiveCount(-2, q[..1]);
    ==
      {
        assert q[0] != -2;
        AppendOne(q, 0);
      }
      1 + 1 + RecursiveCount(-2, q[..0]);
    }
  }
  // assert-end

// impl-end
}

lemma AppendOne<T>(q: seq<T>, n: nat)
  // pre-conditions-start
  requires n < |q|
  // pre-conditions-end
  // post-conditions-start
  ensures q[..n] + [q[n]] == q[..n + 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

function RecursivePositiveProduct(q: seq<int>): int
  decreases |q|
{
  if q == [] then
    1
  else if q[0] <= 0 then
    RecursivePositiveProduct(q[1..])
  else
    q[0] * RecursivePositiveProduct(q[1..])
}
// pure-end

function RecursiveCount(key: int, q: seq<int>): int
  decreases |q|
{
  if q == [] then
    0
  else if q[|q| - 1] == key then
    1 + RecursiveCount(key, q[..|q| - 1])
  else
    RecursiveCount(key, q[..|q| - 1])
}
// pure-end

method ProdAndCount(q: seq<int>, key: int)
    returns (prod: int, count: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures prod == RecursivePositiveProduct(q)
  ensures count == RecursiveCount(key, q)
  // post-conditions-end
{
// impl-start
  prod := 1;
  count := 0;
  var size := |q|;
  var i := 0;
  var curr := 0;
  while i < size
    // invariants-start

    invariant 0 <= i <= size && count == RecursiveCount(key, q[..i]) && prod == RecursivePositiveProduct(q[..i])
    decreases size - i
    // invariants-end

  {
    // assert-start
    Lemma_Count_Inv(q, i, count, key);
    // assert-end

    // assert-start
    Lemma_Prod_Inv(q, i, prod);
    // assert-end

    curr := q[i];
    if curr > 0 {
      prod := prod * curr;
    }
    if curr == key {
      count := count + 1;
    }
    i := i + 1;
  }
  // assert-start
  Lemma_Count_Finish(q, i, count, key);
  // assert-end

  // assert-start
  Lemma_Prod_Finish(q, i, prod);
  // assert-end

// impl-end
}

function county(elem: int, key: int): int
{
  if elem == key then
    1
  else
    0
}
// pure-end

function prody(elem: int): int
{
  if elem <= 0 then
    1
  else
    elem
}
// pure-end

lemma Lemma_Count_Inv(q: seq<int>, i: nat, count: int, key: int)
  // pre-conditions-start
  requires 0 <= i < |q| && count == RecursiveCount(key, q[..i])
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i + 1 <= |q| && county(q[i], key) + count == RecursiveCount(key, q[..i + 1])
  // post-conditions-end
{
// impl-start
  assert q[..i + 1] == q[..i] + [q[i]];
  var q1 := q[..i + 1];
  calc {
    RecursiveCount(key, q[..i + 1]);
  ==
    if q1 == [] then 0 else if q1[i] == key then 1 + RecursiveCount(key, q1[..i]) else RecursiveCount(key, q1[..i]);
  ==
    {
      assert q1 != [];
    }
    if q1[i] == key then 1 + RecursiveCount(key, q1[..i]) else RecursiveCount(key, q1[..i]);
  ==
    {
      KibutzLaw1(q1, key, i);
    }
    (if q1[i] == key then 1 else 0) + RecursiveCount(key, q1[..i]);
  ==
    county(q1[i], key) + RecursiveCount(key, q1[..i]);
  ==
    county(q[i], key) + RecursiveCount(key, q[..i]);
  }
// impl-end
}

lemma Lemma_Prod_Inv(q: seq<int>, i: nat, prod: int)
  // pre-conditions-start
  requires 0 <= i < |q| && prod == RecursivePositiveProduct(q[..i])
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i + 1 <= |q| && prody(q[i]) * prod == RecursivePositiveProduct(q[..i + 1])
  // post-conditions-end
{
// impl-start
  assert q[..i + 1] == q[..i] + [q[i]];
  var q1 := q[..i + 1];
  calc {
    RecursivePositiveProduct(q[..i + 1]);
  ==
    if q1 == [] then 1 else if q1[0] <= 0 then RecursivePositiveProduct(q1[1..]) else q1[0] * RecursivePositiveProduct(q1[1..]);
  ==
    {
      assert q1 != [];
    }
    if q1[0] <= 0 then RecursivePositiveProduct(q1[1..]) else q1[0] * RecursivePositiveProduct(q1[1..]);
  ==
    if q[0] <= 0 then RecursivePositiveProduct(q[1 .. i + 1]) else q[0] * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    {
      KibutzLaw2(q);
    }
    (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    prody(q[0]) * RecursivePositiveProduct(q[1 .. i + 1]);
  ==
    {
      PrependProd(q);
    }
    RecursivePositiveProduct(q[..i + 1]);
  ==
    {
      AppendProd(q[..i + 1]);
    }
    prody(q[i]) * RecursivePositiveProduct(q[..i]);
  ==
    prody(q[i]) * prod;
  }
// impl-end
}

lemma Lemma_Count_Finish(q: seq<int>, i: nat, count: int, key: int)
  // pre-conditions-start
  requires inv: 0 <= i <= |q| && count == RecursiveCount(key, q[..i])
  requires neg_of_guard: i >= |q|
  // pre-conditions-end
  // post-conditions-start
  ensures count == RecursiveCount(key, q)
  // post-conditions-end
{
// impl-start
  assert i <= |q| && count == RecursiveCount(key, q[..i]) by {
    reveal inv;
  }
  assert i == |q| by {
    reveal inv, neg_of_guard;
  }
  assert q[..i] == q[..|q|] == q;
// impl-end
}

lemma Lemma_Prod_Finish(q: seq<int>, i: nat, prod: int)
  // pre-conditions-start
  requires inv: 0 <= i <= |q| && prod == RecursivePositiveProduct(q[..i])
  requires neg_of_guard: i >= |q|
  // pre-conditions-end
  // post-conditions-start
  ensures prod == RecursivePositiveProduct(q)
  // post-conditions-end
{
// impl-start
  assert i <= |q| && prod == RecursivePositiveProduct(q[..i]) by {
    reveal inv;
  }
  assert i == |q| by {
    reveal inv, neg_of_guard;
  }
  assert q[..i] == q[..|q|] == q;
// impl-end
}

lemma KibutzLaw1(q: seq<int>, key: int, i: nat)
  // pre-conditions-start
  requires q != [] && i < |q|
  // pre-conditions-end
  // post-conditions-start
  ensures (if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1])) == (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1])
  // post-conditions-end
{
// impl-start
  if q[|q| - 1] == key {
    calc {
      if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      1 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1]);
    }
  } else {
    calc {
      if q[|q| - 1] == key then 1 + RecursiveCount(key, q[1 .. i + 1]) else 0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      0 + RecursiveCount(key, q[1 .. i + 1]);
    ==
      (if q[|q| - 1] == key then 1 else 0) + RecursiveCount(key, q[1 .. i + 1]);
    }
  }
// impl-end
}

lemma {:verify true} KibutzLaw2(q: seq<int>)
  // pre-conditions-start
  requires q != []
  // pre-conditions-end
  // post-conditions-start
  ensures (if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..])) == (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..])
  // post-conditions-end
{
// impl-start
  if q[0] <= 0 {
    calc {
      if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
    ==
      RecursivePositiveProduct(q[1..]);
    ==
      (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
    }
  } else {
    calc {
      if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
    ==
      q[0] * RecursivePositiveProduct(q[1..]);
    ==
      (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
    }
  }
// impl-end
}

lemma AppendCount(key: int, q: seq<int>)
  // pre-conditions-start
  requires q != []
  // pre-conditions-end
  // post-conditions-start
  ensures RecursiveCount(key, q) == RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key)
  // post-conditions-end
{
// impl-start
  if |q| == 1 {
    assert RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key) == RecursiveCount(key, q[..0]) + county(q[0], key) == RecursiveCount(key, []) + county(q[0], key) == 0 + county(q[0], key) == county(q[0], key);
    assert RecursiveCount(key, q) == county(q[0], key);
  } else {
    var q1 := q[1..];
    calc {
      RecursiveCount(key, q);
    ==
      if q == [] then 0 else if q[|q| - 1] == key then 1 + RecursiveCount(key, q[..|q| - 1]) else RecursiveCount(key, q[..|q| - 1]);
    ==
      RecursiveCount(key, q[..|q| - 1]) + county(q[|q| - 1], key);
    }
  }
// impl-end
}

lemma PrependProd(q: seq<int>)
  // pre-conditions-start
  requires q != []
  // pre-conditions-end
  // post-conditions-start
  ensures RecursivePositiveProduct(q) == prody(q[0]) * RecursivePositiveProduct(q[1..])
  // post-conditions-end
{
// impl-start
  calc {
    RecursivePositiveProduct(q);
  ==
    if q == [] then 1 else if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
  ==
    {
      assert q != [];
    }
    if q[0] <= 0 then RecursivePositiveProduct(q[1..]) else q[0] * RecursivePositiveProduct(q[1..]);
  ==
    {
      KibutzLaw2(q);
    }
    (if q[0] <= 0 then 1 else q[0]) * RecursivePositiveProduct(q[1..]);
  ==
    prody(q[0]) * RecursivePositiveProduct(q[1..]);
  }
// impl-end
}

lemma AppendProd(q: seq<int>)
  // pre-conditions-start
  requires q != []
  // pre-conditions-end
  // post-conditions-start
  ensures RecursivePositiveProduct(q) == RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1])
  // post-conditions-end
{
// impl-start
  if |q| == 1 {
    assert RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1]) == RecursivePositiveProduct(q[..0]) * prody(q[0]) == RecursivePositiveProduct([]) * prody(q[0]) == 1 * prody(q[0]) == prody(q[0]);
    assert RecursivePositiveProduct(q) == prody(q[0]);
  } else {
    var q1 := q[1..];
    calc {
      RecursivePositiveProduct(q);
    ==
      prody(q[0]) * RecursivePositiveProduct(q[1..]);
    ==
      {
        assert q1 != [];
        assert |q1| < |q|;
        AppendProd(q1);
      }
      prody(q[0]) * RecursivePositiveProduct(q1[..|q1| - 1]) * prody(q1[|q1| - 1]);
    ==
      {
        assert q1[..|q1| - 1] == q[1 .. |q| - 1];
        assert q1[|q1| - 1] == q[|q| - 1];
      }
      prody(q[0]) * RecursivePositiveProduct(q[1 .. |q| - 1]) * prody(q[|q| - 1]);
    ==
      {
        PrependProd(q[..|q| - 1]);
      }
      RecursivePositiveProduct(q[..|q| - 1]) * prody(q[|q| - 1]);
    }
  }
// impl-end
}
