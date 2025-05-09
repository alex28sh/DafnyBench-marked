function append(xs: List, ys: List): List
{
  match xs
  case Nil =>
    ys
  case Cons(x, tail) =>
    Cons(x, append(tail, ys))
}
// pure-end

function aval(a: aexp, s: state): val
{
  match a
  case N(n) =>
    n
  case V(x) =>
    s(x)
  case Plus(a0, a1) =>
    aval(a0, s) + aval(a1, s)
}
// pure-end

lemma Example0()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var y := aval(Plus(N(3), V("x")), x => 0);
  assert y == 3;
// impl-end
}

function asimp_const(a: aexp): aexp
{
  match a
  case N(n) =>
    a
  case V(x) =>
    a
  case Plus(a0, a1) =>
    var as0, as1 := asimp_const(a0), asimp_const(a1);
    if as0.N? && as1.N? then
      N(as0.n + as1.n)
    else
      Plus(as0, as1)
}
// pure-end

lemma AsimpConst(a: aexp, s: state)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures aval(asimp_const(a), s) == aval(a, s)
  // post-conditions-end
{
// impl-start
  forall a' | a' < a {
    AsimpConst(a', s);
  }
// impl-end
}

function plus(a0: aexp, a1: aexp): aexp
{
  if a0.N? && a1.N? then
    N(a0.n + a1.n)
  else if a0.N? then
    if a0.n == 0 then
      a1
    else
      Plus(a0, a1)
  else if a1.N? then
    if a1.n == 0 then
      a0
    else
      Plus(a0, a1)
  else
    Plus(a0, a1)
}
// pure-end

lemma AvalPlus(a0: aexp, a1: aexp, s: state)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures aval(plus(a0, a1), s) == aval(a0, s) + aval(a1, s)
  // post-conditions-end
{
// impl-start
// impl-end
}

function asimp(a: aexp): aexp
{
  match a
  case N(n) =>
    a
  case V(x) =>
    a
  case Plus(a0, a1) =>
    plus(asimp(a0), asimp(a1))
}
// pure-end

lemma AsimpCorrect(a: aexp, s: state)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures aval(asimp(a), s) == aval(a, s)
  // post-conditions-end
{
// impl-start
  forall a' | a' < a {
    AsimpCorrect(a', s);
  }
// impl-end
}

lemma ASimplInvolutive(a: aexp)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures asimp(asimp(a)) == asimp(a)
  // post-conditions-end
{
// impl-start
// impl-end
}

function bval(b: bexp, s: state): bool
{
  match b
  case Bc(v) =>
    v
  case Not(b) =>
    !bval(b, s)
  case And(b0, b1) =>
    bval(b0, s) &&
    bval(b1, s)
  case Less(a0, a1) =>
    aval(a0, s) < aval(a1, s)
}
// pure-end

function not(b: bexp): bexp
{
  match b
  case Bc(b0) =>
    Bc(!b0)
  case Not(b0) =>
    b0
  case And(_ /* _v8 */, _ /* _v9 */) =>
    Not(b)
  case Less(_ /* _v10 */, _ /* _v11 */) =>
    Not(b)
}
// pure-end

function and(b0: bexp, b1: bexp): bexp
{
  if b0.Bc? then
    if b0.v then
      b1
    else
      b0
  else if b1.Bc? then
    if b1.v then
      b0
    else
      b1
  else
    And(b0, b1)
}
// pure-end

function less(a0: aexp, a1: aexp): bexp
{
  if a0.N? && a1.N? then
    Bc(a0.n < a1.n)
  else
    Less(a0, a1)
}
// pure-end

function bsimp(b: bexp): bexp
{
  match b
  case Bc(v) =>
    b
  case Not(b0) =>
    not(bsimp(b0))
  case And(b0, b1) =>
    and(bsimp(b0), bsimp(b1))
  case Less(a0, a1) =>
    less(asimp(a0), asimp(a1))
}
// pure-end

lemma BsimpCorrect(b: bexp, s: state)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures bval(bsimp(b), s) == bval(b, s)
  // post-conditions-end
{
// impl-start
  match b
  case {:split false} Bc(v) =>
  case {:split false} Not(b0) =>
    BsimpCorrect(b0, s);
  case {:split false} And(b0, b1) =>
    BsimpCorrect(b0, s);
    BsimpCorrect(b1, s);
  case {:split false} Less(a0, a1) =>
    AsimpCorrect(a0, s);
    AsimpCorrect(a1, s);
// impl-end
}

function exec1(i: instr, s: state, stk: stack): stack
{
  match i
  case LOADI(n) =>
    Cons(n, stk)
  case LOAD(x) =>
    Cons(s(x), stk)
  case ADD =>
    if stk.Cons? && stk.tail.Cons? then
      var Cons(a1, Cons(a0, tail)) := stk;
      Cons(a0 + a1, tail)
    else
      Nil
}
// pure-end

function exec(ii: List<instr>, s: state, stk: stack): stack
{
  match ii
  case Nil =>
    stk
  case Cons(i, rest) =>
    exec(rest, s, exec1(i, s, stk))
}
// pure-end

function comp(a: aexp): List<instr>
{
  match a
  case N(n) =>
    Cons(LOADI(n), Nil)
  case V(x) =>
    Cons(LOAD(x), Nil)
  case Plus(a0, a1) =>
    append(append(comp(a0), comp(a1)), Cons(ADD, Nil))
}
// pure-end

lemma CorrectCompilation(a: aexp, s: state, stk: stack)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exec(comp(a), s, stk) == Cons(aval(a, s), stk)
  // post-conditions-end
{
// impl-start
  match a
  case {:split false} N(n) =>
  case {:split false} V(x) =>
  case {:split false} Plus(a0, a1) =>
    calc {
      exec(comp(a), s, stk);
      exec(append(append(comp(a0), comp(a1)), Cons(ADD, Nil)), s, stk);
      {
        ExecAppend(append(comp(a0), comp(a1)), Cons(ADD, Nil), s, stk);
      }
      exec(Cons(ADD, Nil), s, exec(append(comp(a0), comp(a1)), s, stk));
      {
        ExecAppend(comp(a0), comp(a1), s, stk);
      }
      exec(Cons(ADD, Nil), s, exec(comp(a1), s, exec(comp(a0), s, stk)));
      {
        CorrectCompilation(a0, s, stk);
      }
      exec(Cons(ADD, Nil), s, exec(comp(a1), s, Cons(aval(a0, s), stk)));
      {
        CorrectCompilation(a1, s, Cons(aval(a0, s), stk));
      }
      exec(Cons(ADD, Nil), s, Cons(aval(a1, s), Cons(aval(a0, s), stk)));
      Cons(aval(a1, s) + aval(a0, s), stk);
      Cons(aval(a, s), stk);
    }
// impl-end
}

lemma ExecAppend(ii0: List<instr>, ii1: List<instr>, s: state, stk: stack)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exec(append(ii0, ii1), s, stk) == exec(ii1, s, exec(ii0, s, stk))
  // post-conditions-end
{
// impl-start
// impl-end
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

type vname = string

datatype aexp = N(n: int) | V(vname) | Plus(aexp, aexp)

type val = int

type state = vname -> val

datatype bexp = Bc(v: bool) | Not(bexp) | And(bexp, bexp) | Less(aexp, aexp)

datatype instr = LOADI(val) | LOAD(vname) | ADD

type stack = List<val>
