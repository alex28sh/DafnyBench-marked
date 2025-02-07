function even(n: nat): bool
{
  match n {
    case 0 =>
      true
    case 1 =>
      false
    case _ /* _v0 */ =>
      even(n - 2)
  }
}
// pure-end

lemma a0()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures even(4)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma a1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !even(3)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma a2(n: nat)
  // pre-conditions-start
  requires even(n)
  // pre-conditions-end
  // post-conditions-start
  ensures even(n + 2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma a3(n: nat)
  // pre-conditions-start
  requires even(n + 2)
  // pre-conditions-end
  // post-conditions-start
  ensures even(n)
  // post-conditions-end
{
// impl-start
// impl-end
}

function Even(n: nat): bool
{
  exists r: EvenRule :: 
    r.apply() == n
}
// pure-end

lemma b0()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Even(4)
  // post-conditions-end
{
// impl-start
  assert ev_SS(ev_SS(ev_0)).apply() == 4;
// impl-end
}

lemma b1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !Even(3)
  // post-conditions-end
{
// impl-start
  if r: EvenRule :| r.apply() == 3 {
    assert r.ev_SS? && r.r.apply() == 1;
  }
// impl-end
}

lemma b2(n: nat)
  // pre-conditions-start
  requires Even(n)
  // pre-conditions-end
  // post-conditions-start
  ensures Even(n + 2)
  // post-conditions-end
{
// impl-start
  var r: EvenRule :| r.apply() == n;
  assert ev_SS(r).apply() == n + 2;
// impl-end
}

lemma b3(n: nat)
  // pre-conditions-start
  requires Even(n + 2)
  // pre-conditions-end
  // post-conditions-start
  ensures Even(n)
  // post-conditions-end
{
// impl-start
  var r: EvenRule :| r.apply() == n + 2;
  assert r.ev_SS? && r.r.apply() == n;
// impl-end
}

function Ev(ev: P): bool
{
  ev(0) &&
  forall n: nat | ev(n) :: 
    ev(n + 2)
}
// pure-end

function Minimal(Ev: P -> bool, ev: P): bool
{
  Ev(ev) &&
  forall ev': P, n: nat | Ev(ev') :: 
    ev(n) ==>
      ev'(n)
}
// pure-end

lemma c0(ev: P)
  // pre-conditions-start
  requires Minimal(Ev, ev)
  // pre-conditions-end
  // post-conditions-start
  ensures ev(4)
  // post-conditions-end
{
// impl-start
  assert ev(2);
// impl-end
}

lemma c1(ev: P)
  // pre-conditions-start
  requires Minimal(Ev, ev)
  // pre-conditions-end
  // post-conditions-start
  ensures !ev(3)
  // post-conditions-end
{
// impl-start
  var cex := (n: nat) => n != 1 && n != 3;
  assert Ev(cex);
// impl-end
}

lemma c2(ev: P, n: nat)
  // pre-conditions-start
  requires Minimal(Ev, ev) && ev(n)
  // pre-conditions-end
  // post-conditions-start
  ensures ev(n + 2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma c3(ev: P, n: nat)
  // pre-conditions-start
  requires Minimal(Ev, ev) && ev(n + 2)
  // pre-conditions-end
  // post-conditions-start
  ensures ev(n)
  // post-conditions-end
{
// impl-start
  if !ev(n) {
    var cex := (m: nat) => m != n + 2 && ev(m);
    assert Ev(cex);
  }
// impl-end
}

lemma a_implies_b(n: nat)
  // pre-conditions-start
  requires even(n)
  // pre-conditions-end
  // post-conditions-start
  ensures Even(n)
  // post-conditions-end
{
// impl-start
  if n == 0 {
    assert ev_0.apply() == 0;
  } else {
    a_implies_b(n - 2);
    var r: EvenRule :| r.apply() == n - 2;
    assert ev_SS(r).apply() == n;
  }
// impl-end
}

lemma b_implies_c(ev: P, n: nat)
  // pre-conditions-start
  requires Minimal(Ev, ev) && Even(n)
  // pre-conditions-end
  // post-conditions-start
  ensures ev(n)
  // post-conditions-end
{
// impl-start
  var r: EvenRule :| r.apply() == n;
  if r.ev_SS? {
    assert r.r.apply() == n - 2;
    b_implies_c(ev, n - 2);
  }
// impl-end
}

lemma c_implies_a(ev: P, n: nat)
  // pre-conditions-start
  requires Minimal(Ev, ev) && ev(n)
  // pre-conditions-end
  // post-conditions-start
  ensures even(n)
  // post-conditions-end
{
// impl-start
  if n == 1 {
    var cex := (m: nat) => m != 1;
    assert Ev(cex);
  } else if n >= 2 {
    c3(ev, n - 2);
    c_implies_a(ev, n - 2);
  }
// impl-end
}

datatype EvenRule = ev_0 | ev_SS(r: EvenRule) {
  function apply(): nat
  {
    match this {
      case ev_0 =>
        0
      case ev_SS(r) =>
        r.apply() + 2
    }
  }
// pure-end
}

type P = nat -> bool
