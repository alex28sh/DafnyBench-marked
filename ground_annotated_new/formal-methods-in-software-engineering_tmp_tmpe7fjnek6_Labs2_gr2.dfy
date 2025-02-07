lemma Disc(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures n.Succ? || n.Zero?
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma LPred(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Succ(n).Pred == n
  // post-conditions-end
{
// impl-start
// impl-end
}

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

lemma AddZero(m: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures add(m, Zero) == m
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AddAssoc(m: Nat, n: Nat, p: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures add(m, add(n, p)) == add(add(m, n), p)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AddComm(m: Nat, n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures add(m, n) == add(n, m)
  // post-conditions-end
{
// impl-start
  match m
  case {:split false} Zero =>
    AddZero(n);
  case {:split false} Succ(m') =>
    AddComm(m', n);
// impl-end
}

function lt(m: Nat, n: Nat): bool
{
  (m.Zero? && n.Succ?) || (m.Succ? && n.Succ? && lt(m.Pred, n.Pred))
}
// pure-end

lemma Test1(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures lt(n, Succ(Succ(n)))
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma Test2(n: Nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures n < Succ(n)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma LtTrans(m: Nat, n: Nat, p: Nat)
  // pre-conditions-start
  requires lt(m, n)
  requires lt(n, p)
  // pre-conditions-end
  // post-conditions-start
  ensures lt(m, p)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma Disc2<T>(l: List<T>, a: T)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Cons(a, l).head == a && Cons(a, l).tail == l
  // post-conditions-end
{
// impl-start
// impl-end
}

function size<T>(l: List<T>): nat
{
  match l
  case Nil =>
    0
  case Cons(x, l') =>
    size<T>(l') + 1
}
// pure-end

function app<T>(l1: List<T>, l2: List<T>): List<T>
{
  match l1
  case Nil =>
    l2
  case Cons(x, l1') =>
    Cons(x, app(l1', l2))
}
// pure-end

lemma LenApp<T>(l1: List<T>, l2: List<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures size(app(l1, l2)) == size(l1) + size(l2)
  // post-conditions-end
{
// impl-start
// impl-end
}

function rev<T>(l: List<T>): List<T>
{
  match l
  case Nil =>
    Nil
  case Cons(x, l') =>
    app(rev(l'), Cons(x, Nil))
}
// pure-end

lemma AppNil<T>(l: List<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures app(l, Nil) == l
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma LR1<T>(l: List<T>, x: T)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures rev(app(l, Cons(x, Nil))) == Cons(x, rev(l))
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma RevRev<T>(l: List<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures rev(rev(l)) == l
  // post-conditions-end
{
// impl-start
  match l
  case {:split false} Nil =>
    assert true;
  case {:split false} Cons(x, l') =>
    {
      assert rev(rev(l)) == rev(app(rev(l'), Cons(x, Nil)));
      LR1(rev(l'), x);
    }
// impl-end
}

datatype Nat = Zero | Succ(Pred: Nat)

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
