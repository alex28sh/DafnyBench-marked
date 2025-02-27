function eval(e: Exp, store: map<string, int>): int
{
  match e
  case Const(n) =>
    n
  case Var(s) =>
    if s in store then
      store[s]
    else
      -1
  case Plus(e1, e2) =>
    eval(e1, store) + eval(e2, store)
  case Mult(e1, e2) =>
    eval(e1, store) * eval(e2, store)
}
// pure-end

function optimize(e: Exp): Exp
{
  match e
  case Mult(Const(0), e) =>
    Const(0)
  case Mult(e, Const(0)) =>
    Const(0)
  case Mult(Const(1), e) =>
    e
  case Mult(e, Const(1)) =>
    e
  case Mult(Const(n1), Const(n2)) =>
    Const(n1 * n2)
  case Plus(Const(0), e) =>
    e
  case Plus(e, Const(0)) =>
    e
  case Plus(Const(n1), Const(n2)) =>
    Const(n1 + n2)
  case e =>
    e
}
// pure-end

method optimizeCorrect(e: Exp, s: map<string, int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures eval(e, s) == eval(optimize(e), s)
  // post-conditions-end
{
// impl-start
// impl-end
}

method optimizeFeatures()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert optimize(Mult(Var("x"), Const(0))) == Const(0);
  // assert-end

  // assert-start
  assert optimize(Mult(Var("x"), Const(1))) == Var("x");
  // assert-end

  // assert-start
  assert optimize(Mult(Const(0), Var("x"))) == Const(0);
  // assert-end

  // assert-start
  assert optimize(Mult(Const(1), Var("x"))) == Var("x");
  // assert-end

  // assert-start
  assert optimize(Plus(Const(0), Var("x"))) == Var("x");
  // assert-end

  // assert-start
  assert optimize(Plus(Var("x"), Const(0))) == Var("x");
  // assert-end

  // assert-start
  assert optimize(Plus(Const(3), Const(4))) == Const(7);
  // assert-end

  // assert-start
  assert optimize(Mult(Const(3), Const(4))) == Const(12);
  // assert-end

  // assert-start
  assert optimize(Plus(Plus(Var("x"), Var("y")), Const(0))) == Plus(Var("x"), Var("y"));
  // assert-end

// impl-end
}

datatype Exp = Const(int) | Var(string) | Plus(Exp, Exp) | Mult(Exp, Exp)
