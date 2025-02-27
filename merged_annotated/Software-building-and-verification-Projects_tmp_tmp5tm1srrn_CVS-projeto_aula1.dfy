method factImp(n: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  r := 1;
  var m := n;
  while m > 0
    // invariants-start

    // invariants-end
 {
    r := r * m;
    m := m - 1;
  }
// impl-end
}

function power(n: int, m: nat): int
{
  if m == 0 then
    1
  else
    n * power(n, m - 1)
}
// pure-end

function pow(n: int, m: nat, r: int): int
{
  if m == 0 then
    r
  else
    pow(n, m - 1, r * n)
}
// pure-end

function powerAlt(n: int, m: nat): int
{
  pow(n, m, 1)
}
// pure-end

function equivalentes(n: int, m: nat, r: int): int
  ensures power(n, m) == pow(n, m, r)
// pure-end

lemma l1(n: int, m: nat, r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures equivalentes(n, m, r) == powerAlt(n, m)
  // post-conditions-end

function fact(n: nat): nat
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}
// pure-end

function factAcc(n: nat, a: int): int
  decreases n
{
  if n == 0 then
    a
  else
    factAcc(n - 1, n * a)
}
// pure-end

function factAlt(n: nat): int
{
  factAcc(n, 1)
}
// pure-end

lemma factAcc_correct(n: nat, a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures factAcc(n, a) == fact(n) * a
  // post-conditions-end

lemma equiv(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fact(n) == factAlt(n)
  // post-conditions-end
{
// impl-start
  factAcc_correct(n, 1);
  assert factAcc(n, 1) == fact(n) * 1;
  assert factAlt(n) == factAcc(n, 1);
  assert fact(n) == fact(n) * 1;
// impl-end
}

function mystery1(n: nat, m: nat): nat
  ensures mystery1(n, m) == n + m
  decreases n, m
{
  if n == 0 then
    m
  else
    mystery1(n - 1, m + 1)
}
// pure-end

function mystery2(n: nat, m: nat): nat
  ensures mystery2(n, m) == n + m
  decreases m
{
  if m == 0 then
    n
  else
    mystery2(n + 1, m - 1)
}
// pure-end

function mystery3(n: nat, m: nat): nat
  ensures mystery3(n, m) == n * m
{
  if n == 0 then
    0
  else
    mystery1(m, mystery3(n - 1, m))
}
// pure-end

function mystery4(n: nat, m: nat): nat
  ensures mystery4(n, m) == power(n, m)
{
  if m == 0 then
    1
  else
    mystery3(n, mystery4(n, m - 1))
}
// pure-end
