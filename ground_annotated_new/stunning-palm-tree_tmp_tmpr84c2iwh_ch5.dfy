function More(x: int): int
{
  if x <= 0 then
    1
  else
    More(x - 2) + 3
}
// pure-end

lemma {:induction false} Increasing(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x < More(x)
  // post-conditions-end
{
// impl-start
  if x <= 0 {
  } else {
    Increasing(x - 2);
  }
// impl-end
}

method ExampleLemmaUse(a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var b := More(a);
  // assert-start
  Increasing(a);
  // assert-end

  var c := More(b);
  // assert-start
  Increasing(b);
  // assert-end

  // assert-start
  assert 2 <= c - a;
  // assert-end

// impl-end
}

method ExampleLemmaUse50(a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  Increasing(a);
  // assert-end

  var b := More(a);
  var c := More(b);
  if a < 1000 {
    // assert-start
    Increasing(b);
    // assert-end

    // assert-start
    assert 2 <= c - a;
    // assert-end

  }
  // assert-start
  assert a < 200 ==> 2 <= c - a;
  // assert-end

// impl-end
}

method ExampleLemmaUse51(a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  Increasing(a);
  // assert-end

  var b := More(a);
  // assert-start
  Increasing(b);
  // assert-end

  b := More(b);
  if a < 1000 {
    // assert-start
    assert 2 <= b - a;
    // assert-end

  }
  // assert-start
  assert a < 200 ==> 2 <= b - a;
  // assert-end

// impl-end
}

function Ack(m: nat, n: nat): nat
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}
// pure-end

lemma {:induction false} Ack1n(m: nat, n: nat)
  // pre-conditions-start
  requires m == 1
  // pre-conditions-end
  // post-conditions-start
  ensures Ack(m, n) == n + 2
  // post-conditions-end
{
// impl-start
  if n == 0 {
    calc {
      Ack(m, n);
    ==
      Ack(m - 1, 1);
    ==
      Ack(0, 1);
    ==
      1 + 1;
    ==
      2;
    ==
      n + 2;
    }
  } else {
    calc {
      Ack(m, n);
    ==
      Ack(m - 1, Ack(m, n - 1));
    ==
      Ack(0, Ack(1, n - 1));
    ==
      {
        Ack1n(1, n - 1);
      }
      Ack(0, n - 1 + 2);
    ==
      Ack(0, n + 1);
    ==
      n + 1 + 1;
    ==
      n + 2;
    }
  }
// impl-end
}

function Reduce(m: nat, x: int): int
{
  if m == 0 then
    x
  else
    Reduce(m / 2, x + 1) - m
}
// pure-end

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Reduce(m, x) <= x
  // post-conditions-end
{
// impl-start
  if m == 0 {
    assert Reduce(0, x) == x;
  } else {
    calc {
      Reduce(m, x);
    ==
      Reduce(m / 2, x + 1) - m;
    <=
      {
        ReduceUpperBound(m / 2, x + 1);
      }
      Reduce(m / 2, x + 1) - m + x + 1 - Reduce(m / 2, x + 1);
    ==
      x - m + 1;
    <=
      {
        assert m >= 1;
      }
      x;
    }
  }
// impl-end
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x - 2 * m <= Reduce(m, x)
  // post-conditions-end
{
// impl-start
  if m == 0 {
    assert x - 2 * 0 <= x == Reduce(0, x);
  } else {
    calc {
      Reduce(m, x);
    ==
      Reduce(m / 2, x + 1) - m;
    >=
      {
        ReduceLowerBound(m / 2, x + 1);
        assert x + 1 - m <= Reduce(m / 2, x + 1);
      }
      x + 1 - 2 * m;
    >
      x - 2 * m;
    }
  }
// impl-end
}

function Eval(e: Expr, env: map<string, nat>): nat
{
  match e {
    case Const(c) =>
      c
    case Var(s) =>
      if s in env then
        env[s]
      else
        0
    case Node(op, args) =>
      EvalList(op, args, env)
  }
}
// pure-end

function Unit(op: Op): nat
{
  match op
  case Add =>
    0
  case Mul =>
    1
}
// pure-end

function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
  decreases args, op, env
{
  match args {
    case Nil =>
      Unit(op)
    case Cons(e, tail) =>
      var v0, v1 := Eval(e, env), EvalList(op, tail, env);
      match op
      case Add =>
        v0 + v1
      case Mul =>
        v0 * v1
  }
}
// pure-end

function Substitute(e: Expr, n: string, c: nat): Expr
{
  match e
  case Const(_ /* _v2 */) =>
    e
  case Var(s) =>
    if s == n then
      Const(c)
    else
      e
  case Node(op, args) =>
    Node(op, SubstituteList(args, n, c))
}
// pure-end

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
  match es
  case Nil =>
    Nil
  case Cons(head, tail) =>
    Cons(Substitute(head, n, c), SubstituteList(tail, n, c))
}
// pure-end

lemma {:induction false} EvalSubstituteCorrect(e: Expr, n: string, c: nat, env: map<string, nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
  // post-conditions-end
{
// impl-start
  match e
  case {:split false} Const(_ /* _v3 */) =>
    {
    }
  case {:split false} Var(s) =>
    {
      calc {
        Eval(Substitute(e, n, c), env);
        Eval(if s == n then Const(c) else e, env);
        if s == n then Eval(Const(c), env) else Eval(e, env);
        if s == n then c else Eval(e, env);
        if s == n then c else Eval(e, env[n := c]);
        if s == n then Eval(e, env[n := c]) else Eval(e, env[n := c]);
        Eval(e, env[n := c]);
      }
    }
  case {:split false} Node(op, args) =>
    {
      EvalSubstituteListCorrect(op, args, n, c, env);
    }
// impl-end
}

lemma {:induction false} EvalSubstituteListCorrect(op: Op, args: List<Expr>, n: string, c: nat, env: map<string, nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures EvalList(op, SubstituteList(args, n, c), env) == EvalList(op, args, env[n := c])
  decreases args, op, n, c, env
  // post-conditions-end
{
// impl-start
  match args
  case {:split false} Nil =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      calc {
        EvalList(op, SubstituteList(args, n, c), env);
      ==
        EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
      ==
        EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
      ==
        match op case Add => Eval(Substitute(head, n, c), env) + EvalList(op, SubstituteList(tail, n, c), env) case Mul => Eval(Substitute(head, n, c), env) * EvalList(op, SubstituteList(tail, n, c), env);
      ==
        {
          EvalSubstituteCorrect(head, n, c, env);
        }
        match op case Add => Eval(head, env[n := c]) + EvalList(op, SubstituteList(tail, n, c), env) case Mul => Eval(head, env[n := c]) * EvalList(op, SubstituteList(tail, n, c), env);
      ==
        {
          EvalSubstituteListCorrect(op, tail, n, c, env);
        }
        match op case Add => Eval(head, env[n := c]) + EvalList(op, tail, env[n := c]) case Mul => Eval(head, env[n := c]) * EvalList(op, tail, env[n := c]);
      ==
        EvalList(op, args, env[n := c]);
      }
    }
// impl-end
}

lemma EvalEnv(e: Expr, n: string, env: map<string, nat>)
  // pre-conditions-start
  requires n in env.Keys
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
  // post-conditions-end
{
// impl-start
  match e
  case {:split false} Const(_ /* _v4 */) =>
    {
    }
  case {:split false} Var(s) =>
    {
    }
  case {:split false} Node(op, args) =>
    {
      match args
      case {:split false} Nil =>
        {
        }
      case {:split false} Cons(head, tail) =>
        {
          EvalEnv(head, n, env);
          EvalEnvList(op, tail, n, env);
        }
    }
// impl-end
}

lemma EvalEnvList(op: Op, es: List<Expr>, n: string, env: map<string, nat>)
  // pre-conditions-start
  requires n in env.Keys
  // pre-conditions-end
  // post-conditions-start
  ensures EvalList(op, es, env) == EvalList(op, SubstituteList(es, n, env[n]), env)
  decreases es, op, n, env
  // post-conditions-end
{
// impl-start
  match es
  case {:split false} Nil =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      EvalEnv(head, n, env);
      EvalEnvList(op, tail, n, env);
    }
// impl-end
}

lemma EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
  // pre-conditions-start
  requires n !in env.Keys
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
  // post-conditions-end
{
// impl-start
  match e
  case {:split false} Const(_ /* _v5 */) =>
    {
    }
  case {:split false} Var(s) =>
    {
    }
  case {:split false} Node(op, args) =>
    {
      calc {
        Eval(Substitute(e, n, 0), env);
        EvalList(op, SubstituteList(args, n, 0), env);
      ==
        {
          EvalEnvDefaultList(op, args, n, env);
        }
        EvalList(op, args, env);
        Eval(e, env);
      }
    }
// impl-end
}

lemma EvalEnvDefaultList(op: Op, args: List<Expr>, n: string, env: map<string, nat>)
  // pre-conditions-start
  requires n !in env.Keys
  // pre-conditions-end
  // post-conditions-start
  ensures EvalList(op, args, env) == EvalList(op, SubstituteList(args, n, 0), env)
  decreases args, op, n, env
  // post-conditions-end
{
// impl-start
  match args
  case {:split false} Nil =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      EvalEnvDefault(head, n, env);
      EvalEnvDefaultList(op, tail, n, env);
    }
// impl-end
}

lemma SubstituteIdempotent(e: Expr, n: string, c: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Substitute(Substitute(e, n, c), n, c) == Substitute(e, n, c)
  // post-conditions-end
{
// impl-start
  match e
  case {:split false} Const(_ /* _v6 */) =>
    {
    }
  case {:split false} Var(_ /* _v7 */) =>
    {
    }
  case {:split false} Node(op, args) =>
    {
      SubstituteListIdempotent(args, n, c);
    }
// impl-end
}

lemma SubstituteListIdempotent(args: List<Expr>, n: string, c: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SubstituteList(SubstituteList(args, n, c), n, c) == SubstituteList(args, n, c)
  // post-conditions-end
{
// impl-start
  match args
  case {:split false} Nil =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      SubstituteIdempotent(head, n, c);
      SubstituteListIdempotent(tail, n, c);
    }
// impl-end
}

function Optimize(e: Expr): Expr
{
  if e.Node? then
    var args := OptimizeAndFilter(e.args, Unit(e.op));
    Shorten(e.op, args)
  else
    e
}
// pure-end

lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(Optimize(e), env) == Eval(e, env)
  // post-conditions-end
{
// impl-start
  if e.Node? {
    OptimizeAndFilterCorrect(e.args, e.op, env);
    ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env);
  }
// impl-end
}

function OptimizeAndFilter(args: List<Expr>, u: nat): List<Expr>
{
  match args
  case Nil =>
    Nil
  case Cons(head, tail) =>
    var hd, tl := Optimize(head), OptimizeAndFilter(tail, u);
    if hd == Const(u) then
      tl
    else
      Cons(hd, tl)
}
// pure-end

lemma OptimizeAndFilterCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env) == Eval(Node(op, args), env)
  // post-conditions-end
{
// impl-start
  match args
  case {:split false} Nil =>
    {
    }
  case {:split false} Cons(head, tail) =>
    {
      OptimizeCorrect(head, env);
      OptimizeAndFilterCorrect(tail, op, env);
    }
// impl-end
}

lemma EvalListUnitHead(head: Expr, tail: List<Expr>, op: Op, env: map<string, nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(head, env) == Unit(op) ==> EvalList(op, Cons(head, tail), env) == EvalList(op, tail, env)
  // post-conditions-end
{
// impl-start
  var ehead, etail := Eval(head, env), EvalList(op, tail, env);
  if ehead == Unit(op) {
    match op
    case {:split false} Add =>
      {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==
          ehead + etail;
        ==
          etail;
        }
      }
    case {:split false} Mul =>
      {
        calc {
          EvalList(op, Cons(head, tail), env);
        ==
          ehead * etail;
        ==
          etail;
        }
      }
  }
// impl-end
}

function Shorten(op: Op, args: List<Expr>): Expr
{
  match args
  case Nil =>
    Const(Unit(op))
  case Cons(head, Nil) =>
    head
  case _ /* _v8 */ =>
    Node(op, args)
}
// pure-end

lemma ShortenCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env)
  // post-conditions-end
{
// impl-start
  match args
  case {:split false} Nil =>
    {
    }
  case {:split false} Cons(head, Nil) =>
    {
      calc {
        Eval(Node(op, args), env);
        EvalList(op, Cons(head, Nil), env);
        Eval(head, env);
      }
    }
  case {:split false} _ /* _v9 */ =>
    {
    }
// impl-end
}

datatype Expr = Const(nat) | Var(string) | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
