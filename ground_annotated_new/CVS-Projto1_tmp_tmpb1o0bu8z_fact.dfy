function fact(n: nat): nat
  decreases n
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
  ensures factAcc(n, a) == a * fact(n)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma factAlt_correct(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures factAlt(n) == fact(n)
  // post-conditions-end
{
// impl-start
  factAcc_correct(n, 1);
  assert factAcc(n, 1) == 1 * fact(n);
  assert 1 * fact(n) == fact(n);
  assert factAlt(n) == factAcc(n, 1);
// impl-end
}

function length<T>(l: List<T>): nat
  decreases l
{
  match l
  case Nil =>
    0
  case Cons(_ /* _v2 */, r) =>
    1 + length(r)
}
// pure-end

lemma {:induction false} length_non_neg<T>(l: List<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures length(l) >= 0
  // post-conditions-end
{
// impl-start
  match l
  case {:split false} Nil =>
  case {:split false} Cons(_ /* _v3 */, r) =>
    length_non_neg(r);
    assert length(r) >= 0;
    assert 1 + length(r) >= 0;
    assert 1 + length(r) == length(l);
// impl-end
}

function lengthTL<T>(l: List<T>, acc: nat): nat
{
  match l
  case Nil =>
    acc
  case Cons(_ /* _v4 */, r) =>
    lengthTL(r, 1 + acc)
}
// pure-end

lemma {:induction false} lengthTL_aux<T>(l: List<T>, acc: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures lengthTL(l, acc) == acc + length(l)
  // post-conditions-end
{
// impl-start
  match l
  case {:split false} Nil =>
    assert acc + length<T>(Nil) == acc;
  case {:split false} Cons(_ /* _v5 */, r) =>
    lengthTL_aux(r, acc + 1);
// impl-end
}

lemma lengthEq<T>(l: List<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures length(l) == lengthTL(l, 0)
  // post-conditions-end
{
// impl-start
  lengthTL_aux(l, 0);
// impl-end
}

datatype List<T> = Nil | Cons(T, List<T>)
