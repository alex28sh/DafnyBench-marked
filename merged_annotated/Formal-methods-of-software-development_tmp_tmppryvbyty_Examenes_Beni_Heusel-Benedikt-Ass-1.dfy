function exp(x: int, e: nat): int
{
  if e == 0 then
    1
  else
    x * exp(x, e - 1)
}
// pure-end

lemma div10_Lemma(n: nat)
  // pre-conditions-start
  requires n >= 3
  // pre-conditions-end
  // post-conditions-start
  ensures (exp(3, 4 * n) + 9) % 10 == 0
  // post-conditions-end
{
// impl-start
  if n == 3 {
    calc {
      exp(3, 4 * n) + 9;
      exp(3, 4 * 3) + 9;
      exp(3, 12) + 9;
      531441 + 9;
      531450;
      10 * 53145;
    }
  } else {
    div10_Lemma(n - 1);
    var k := (exp(3, 4 * (n - 1)) + 9) / 10;
    assert 10 * k == exp(3, 4 * (n - 1)) + 9;
    calc {
      exp(3, 4 * n) + 9;
      3 * 3 * exp(3, 4 * n - 2) + 9;
      3 * 3 * 3 * 3 * exp(3, 4 * n - 4) + 9;
      81 * exp(3, 4 * n - 4) + 9;
      81 * exp(3, 4 * (n - 1)) + 9;
      80 * exp(3, 4 * (n - 1)) + (exp(3, 4 * (n - 1)) + 9);
      80 * exp(3, 4 * (n - 1)) + 10 * k;
      10 * (8 * exp(3, 4 * (n - 1)) + k);
    }
  }
// impl-end
}

lemma div10Forall_Lemma()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall n :: n >= 3 ==> (exp(3, 4 * n) + 9) % 10 == 0
  // post-conditions-end
{
// impl-start
  forall n | n >= 3 {
    div10_Lemma(n);
  }
// impl-end
}

function sumSerie(x: int, n: nat): int
{
  if n == 0 then
    1
  else
    sumSerie(x, n - 1) + exp(x, n)
}
// pure-end

lemma {:induction false} sumSerie_Lemma(x: int, n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (1 - x) * sumSerie(x, n) == 1 - exp(x, n + 1)
  // post-conditions-end
{
// impl-start
  if n == 0 {
    calc {
      (1 - x) * sumSerie(x, n);
      (1 - x) * sumSerie(x, 0);
      (1 - x) * 1;
      1 - x;
      1 - exp(x, 1);
      1 - exp(x, n + 1);
    }
  } else {
    calc {
      (1 - x) * sumSerie(x, n);
      (1 - x) * (sumSerie(x, n - 1) + exp(x, n));
      (1 - x) * sumSerie(x, n - 1) + (1 - x) * exp(x, n);
      {
        sumSerie_Lemma(x, n - 1);
      }
      1 - exp(x, n) + (1 - x) * exp(x, n);
      1 - exp(x, n) + exp(x, n) - x * exp(x, n);
      1 - x * exp(x, n);
      1 - exp(x, n + 1);
    }
  }
// impl-end
}

lemma notSq_Lemma(n: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !exists z :: z * z == 4 * n + 2
  // post-conditions-end
{
// impl-start
  if exists z :: 4 * n + 2 == z * z {
    var z :| z * z == 4 * n + 2 == z * z;
    if z % 2 == 0 {
      var k := z / 2;
      assert z == 2 * k;
      calc ==> {
        4 * n + 2 == z * z;
        4 * n + 2 == 2 * k * (2 * k);
        2 * (2 * n + 1) == 2 * (2 * k * k);
        2 * n + 1 == 2 * k * k;
        2 * n + 1 == 2 * (k * k);
      }
      assert 0 == 2 * (k * k) % 2 == (2 * n + 1) % 2 == 1;
      assert false;
    } else {
      var k := (z - 1) / 2;
      assert z == 2 * k + 1;
      calc ==> {
        4 * n + 2 == z * z;
        4 * n + 2 == (2 * k + 1) * (2 * k + 1);
        4 * n + 2 == 4 * k * k + 4 * k + 1;
        4 * n + 2 == 2 * (2 * k * k + 2 * k) + 1;
        2 * (2 * n + 1) == 2 * (2 * k * k + 2 * k) + 1;
      }
      assert 0 == 2 * (2 * n + 1) % 2 == (2 * (2 * k * k + 2 * k) + 1) % 2 == 1;
      assert false;
    }
  }
// impl-end
}

lemma oneIsEven_Lemma(x: int, y: int, z: int)
  // pre-conditions-start
  requires z * z == x * x + y * y
  // pre-conditions-end
  // post-conditions-start
  ensures x % 2 == 0 || y % 2 == 0
  // post-conditions-end
{
// impl-start
  if !(x % 2 == 0 || y % 2 == 0) {
    assert x == 2 * ((x - 1) / 2) + 1;
    var k: int :| 2 * k + 1 == x;
    assert y == 2 * ((y - 1) / 2) + 1;
    var b: int :| 2 * b + 1 == y;
    calc {
      x * x + y * y;
      (2 * k + 1) * (2 * k + 1) + (2 * b + 1) * (2 * b + 1);
      4 * k * k + 4 * k + 1 + (2 * b + 1) * (2 * b + 1);
      4 * k * k + 4 * k + 1 + 4 * b * b + 4 * b + 1;
      4 * k * k + 4 * k + 4 * b * b + 4 * b + 2;
      4 * (k * k + k + b * b + b) + 2;
    }
    assert z * z == 4 * (k * k + k + b * b + b) + 2;
    notSq_Lemma(k * k + k + b * b + b);
    assert false;
  }
// impl-end
}

lemma exp_Lemma(x: int, e: nat)
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

lemma prod_Lemma(z: int, a: int, b: int)
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

lemma expPlus1_Lemma(x: int, n: nat)
  // pre-conditions-start
  requires x >= 1 && n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures exp(x + 1, n) >= exp(x, n) + 1
  // post-conditions-end
{
// impl-start
  if n == 1 {
    calc {
      exp(x + 1, n);
    ==
      exp(x + 1, 1);
    ==
      x + 1;
    >=
      x + 1;
    ==
      exp(x, 1) + 1;
    ==
      exp(x, n) + 1;
    }
  } else {
    calc {
      exp(x + 1, n);
    ==
      (x + 1) * exp(x + 1, n - 1);
    >=
      {
        expPlus1_Lemma(x, n - 1);
      }
      (x + 1) * (exp(x, n - 1) + 1);
    ==
      x * exp(x, n - 1) + x + exp(x, n - 1) + 1;
    ==
      exp(x, n) + x + exp(x, n - 1) + 1;
    ==
      exp(x, n) + 1 + exp(x, n - 1) + x;
    >=
      {
        exp_Lemma(x, n - 1);
      }
      exp(x, n) + 1;
    }
  }
// impl-end
}
