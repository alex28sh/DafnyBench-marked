function f(x: int): int
// pure-end

function ff(x: int): int
// pure-end

lemma {:axiom} ff_eq()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x {:trigger ff(x)} :: ff(x) == f(f(x))
  // post-conditions-end

lemma {:axiom} ff_eq2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x {:trigger f(f(x))} :: ff(x) == f(f(x))
  // post-conditions-end

lemma {:axiom} ff_eq_bad()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x {:trigger {f(x)}} :: ff(x) == f(f(x))
  // post-conditions-end

lemma use_ff(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  ff_eq();
  assert f(ff(x)) == ff(f(x));
// impl-end
}

lemma use_ff2(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  ff_eq2();
  assert f(f(x)) == ff(x);
  assert f(ff(x)) == ff(f(x));
// impl-end
}
