lemma EcCuadDiv2_Lemma(x: int)
  // pre-conditions-start
  requires x >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures (x * x + x) % 2 == 0
  // post-conditions-end
{
// impl-start
  if x != 1 {
    EcCuadDiv2_Lemma(x - 1);
    assert x * x + x == (x - 1) * (x - 1) + (x - 1) + 2 * x;
  }
// impl-end
}

lemma EcCubicaDiv6_Lemma(x: int)
  // pre-conditions-start
  requires x >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures (x * x * x + 3 * x * x + 2 * x) % 6 == 0
  // post-conditions-end
{
// impl-start
  if x > 1 {
    EcCubicaDiv6_Lemma(x - 1);
    assert (x * x * x - 3 * x * x + 3 * x - 1 + 3 * x * x - 6 * x + 3 + 2 * x - 2) % 6 == 0;
    assert (x * x * x - x) % 6 == 0;
    assert x * x * x + 3 * x * x + 2 * x == x * x * x - x + 3 * (x * x + x);
    EcCuadDiv2_Lemma(x);
  }
// impl-end
}

lemma cubEven_Lemma(x: int)
  // pre-conditions-start
  requires (x * x * x + 5) % 2 == 1
  // pre-conditions-end
  // post-conditions-start
  ensures x % 2 == 0
  // post-conditions-end
{
// impl-start
  if x % 2 == 1 {
    var k := (x - 1) / 2;
    assert x * x * x + 5 == (2 * k + 1) * (2 * k + 1) * (2 * k + 1) + 5 == 8 * k * k * k + 12 * k * k + 6 * k + 6 == 2 * (4 * k * k * k + 6 * k * k + 3 * k + 3);
    assert false;
  }
// impl-end
}

lemma perfectCube_Lemma(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists z :: x * x * x == 3 * z || x * x * x == 3 * z + 1 || x * x * x == 3 * z - 1
  // post-conditions-end
{
// impl-start
  if x % 3 == 0 {
    var k := x / 3;
    assert x * x * x == 27 * k * k * k == 3 * (9 * k * k * k);
  } else if x % 3 == 1 {
    var k := (x - 1) / 3;
    assert x * x * x == (3 * k + 1) * (3 * k + 1) * (3 * k + 1) == 27 * k * k * k + 27 * k * k + 9 * k + 1;
    assert x * x * x == 3 * (9 * k * k * k + 9 * k * k + 3 * k) + 1;
  } else {
    var k := (x - 2) / 3;
    assert x * x * x == (3 * k + 2) * (3 * k + 2) * (3 * k + 2) == 27 * k * k * k + 54 * k * k + 36 * k + 8;
    assert x * x * x == 3 * (9 * k * k * k + 18 * k * k + 12 * k + 3) - 1;
  }
// impl-end
}

function exp(x: int, e: nat): int
{
  if e == 0 then
    1
  else
    x * exp(x, e - 1)
}
// pure-end

lemma expGET1_Lemma(x: int, e: nat)
  // pre-conditions-start
  requires x >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures exp(x, e) >= 1
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma prodMon_Lemma(z: int, a: int, b: int)
  // pre-conditions-start
  requires z >= 1 && a >= b >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures z * a >= z * b
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma expMon_Lemma(x: int, n: nat)
  // pre-conditions-start
  requires x >= 1 && n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures exp(x + 1, n) >= exp(x, n) + 1
  // post-conditions-end
{
// impl-start
  if n != 1 {
    calc {
      exp(x + 1, n);
    ==
      (x + 1) * exp(x + 1, n - 1);
    ==
      x * exp(x + 1, n - 1) + exp(x + 1, n - 1);
    >=
      {
        expGET1_Lemma(x + 1, n - 1);
      }
      x * exp(x + 1, n - 1);
    >=
      {
        expMon_Lemma(x, n - 1);
        expGET1_Lemma(x + 1, n - 1);
        expGET1_Lemma(x, n - 1);
        prodMon_Lemma(x, exp(x + 1, n - 1), exp(x, n - 1) + 1);
      }
      x * (exp(x, n - 1) + 1);
    ==
      x * exp(x, n - 1) + x;
    >=
      exp(x, n) + 1;
    }
  }
// impl-end
}
