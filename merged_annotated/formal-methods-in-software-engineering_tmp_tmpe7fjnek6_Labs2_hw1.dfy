function add(m: Nat, n: Nat): Nat
  decreases m
{
  match m
  case Zero =>
    n
  case Succ(m') =>
    Succ(add(m', n))
}
// pure-end

function Odd(m: Nat): bool
  decreases m
{
  match m
  case Zero =>
    false
  case Succ(m') =>
    Even(m')
}
// pure-end

function Even(m: Nat): bool
  decreases m
{
  match m
  case Zero =>
    true
  case Succ(m') =>
    Odd(m')
}
// pure-end

lemma SumMNIsEven(m: Nat, n: Nat)
  // pre-conditions-start
  requires Odd(m)
  requires Odd(n)
  // pre-conditions-end
  // post-conditions-start
  ensures Even(add(m, n))
  // post-conditions-end
{
// impl-start
  match m
  case {:split false} Succ(Zero) =>
    assert Even(add(Succ(Zero), n));
  case {:split false} Succ(Succ(m')) =>
    SumMNIsEven(m', n);
// impl-end
}

datatype Nat = Zero | Succ(Pred: Nat)
