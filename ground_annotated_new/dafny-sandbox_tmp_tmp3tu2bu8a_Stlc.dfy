function value(t: tm): bool
{
  t.tabs?
}
// pure-end

function fv(t: tm): set<int>
{
  match t
  case tvar(id) =>
    {id}
  case tabs(x, T, body) =>
    fv(body) - {x}
  case tapp(f, arg) =>
    fv(f) + fv(arg)
}
// pure-end

function subst(x: int, s: tm, t: tm): tm
{
  match t
  case tvar(x') =>
    if x == x' then
      s
    else
      t
  case tabs(x', T, t1) =>
    tabs(x', T, if x == x' then t1 else subst(x, s, t1))
  case tapp(t1, t2) =>
    tapp(subst(x, s, t1), subst(x, s, t2))
}
// pure-end

function step(t: tm): option<tm>
{
  if t.tapp? && t.f.tabs? && value(t.arg) then
    Some(subst(t.f.x, t.arg, t.f.body))
  else if t.tapp? && step(t.f).Some? then
    Some(tapp(step(t.f).get, t.arg))
  else if t.tapp? && value(t.f) && step(t.arg).Some? then
    Some(tapp(t.f, step(t.arg).get))
  else
    None
}
// pure-end

function reduces_to(t: tm, t': tm, n: nat): bool
  decreases n
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n - 1))
}
// pure-end

lemma lemma_step_example1(n: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))), tabs(0, TBase, tvar(0)), n)
  // post-conditions-end
{
// impl-start
// impl-end
}

function find(c: map<int, ty>, x: int): option<ty>
{
  if x in c then
    Some(c[x])
  else
    None
}
// pure-end

function extend(x: int, T: ty, c: map<int, ty>): map<int, ty>
{
  c[x := T]
}
// pure-end

function has_type(c: map<int, ty>, t: tm): option<ty>
  decreases t
{
  match t
  case tvar(id) =>
    find(c, id)
  case tabs(x, T, body) =>
    var ty_body := has_type(extend(x, T, c), body);
    if ty_body.Some? then
      Some(TArrow(T, ty_body.get))
    else
      None
  case tapp(f, arg) =>
    var ty_f := has_type(c, f);
    var ty_arg := has_type(c, arg);
    if ty_f.Some? && ty_arg.Some? then
      if ty_f.get.TArrow? && ty_f.get.T1 == ty_arg.get then
        Some(ty_f.get.T2)
      else
        None
    else
      None
}
// pure-end

lemma example_typing_1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase))
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma example_typing_2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) == Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)))
  // post-conditions-end
{
// impl-start
  var c := extend(1, TArrow(TBase, TBase), extend(0, TBase, map[]));
  assert find(c, 0) == Some(TBase);
  assert has_type(c, tvar(0)) == Some(TBase);
  assert has_type(c, tvar(1)) == Some(TArrow(TBase, TBase));
  assert has_type(c, tapp(tvar(1), tapp(tvar(1), tvar(0)))) == Some(TBase);
// impl-end
}

lemma nonexample_typing_1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None
  // post-conditions-end
{
// impl-start
  var c := extend(1, TBase, extend(0, TBase, map[]));
  assert find(c, 0) == Some(TBase);
  assert has_type(c, tapp(tvar(0), tvar(1))) == None;
// impl-end
}

lemma nonexample_typing_3(S: ty, T: ty)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T)
  // post-conditions-end
{
// impl-start
  var c := extend(0, S, map[]);
  assert has_type(c, tapp(tvar(0), tvar(0))) == None;
// impl-end
}

lemma theorem_progress(t: tm)
  // pre-conditions-start
  requires has_type(map[], t).Some?
  // pre-conditions-end
  // post-conditions-start
  ensures value(t) || step(t).Some?
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma {:induction c, t} lemma_free_in_context(c: map<int, ty>, x: int, t: tm)
  // pre-conditions-start
  requires x in fv(t)
  requires has_type(c, t).Some?
  // pre-conditions-end
  // post-conditions-start
  ensures find(c, x).Some?
  decreases t
  // post-conditions-end
{
// impl-start
// impl-end
}

function closed(t: tm): bool
{
  forall x :: 
    x !in fv(t)
}
// pure-end

lemma corollary_typable_empty__closed(t: tm)
  // pre-conditions-start
  requires has_type(map[], t).Some?
  // pre-conditions-end
  // post-conditions-start
  ensures closed(t)
  // post-conditions-end
{
// impl-start
  forall x: int | true
    ensures x !in fv(t)
  {
    if x in fv(t) {
      lemma_free_in_context(map[], x, t);
      assert false;
    }
  }
// impl-end
}

lemma {:induction t} lemma_context_invariance(c: map<int, ty>, c': map<int, ty>, t: tm)
  // pre-conditions-start
  requires has_type(c, t).Some?
  requires forall x: int :: x in fv(t) ==> find(c, x) == find(c', x)
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(c, t) == has_type(c', t)
  decreases t
  // post-conditions-end
{
// impl-start
  if t.tabs? {
    assert fv(t.body) == fv(t) || fv(t.body) == fv(t) + {t.x};
    lemma_context_invariance(extend(t.x, t.T, c), extend(t.x, t.T, c'), t.body);
  }
// impl-end
}

lemma lemma_substitution_preserves_typing(c: map<int, ty>, x: int, s: tm, t: tm)
  // pre-conditions-start
  requires has_type(map[], s).Some?
  requires has_type(extend(x, has_type(map[], s).get, c), t).Some?
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(c, subst(x, s, t)) == has_type(extend(x, has_type(map[], s).get, c), t)
  decreases t
  // post-conditions-end
{
// impl-start
  var S := has_type(map[], s).get;
  var cs := extend(x, S, c);
  var T := has_type(cs, t).get;
  if t.tvar? {
    if t.id == x {
      assert T == S;
      corollary_typable_empty__closed(s);
      lemma_context_invariance(map[], c, s);
    }
  }
  if t.tabs? {
    if t.x == x {
      lemma_context_invariance(cs, c, t);
    } else {
      var cx := extend(t.x, t.T, c);
      var csx := extend(x, S, cx);
      var cxs := extend(t.x, t.T, cs);
      lemma_context_invariance(cxs, csx, t.body);
      lemma_substitution_preserves_typing(cx, x, s, t.body);
    }
  }
// impl-end
}

lemma theorem_preservation(t: tm)
  // pre-conditions-start
  requires has_type(map[], t).Some?
  requires step(t).Some?
  // pre-conditions-end
  // post-conditions-start
  ensures has_type(map[], step(t).get) == has_type(map[], t)
  // post-conditions-end
{
// impl-start
  if t.tapp? && value(t.f) && value(t.arg) {
    lemma_substitution_preserves_typing(map[], t.f.x, t.arg, t.f.body);
  }
// impl-end
}

function normal_form(t: tm): bool
{
  step(t).None?
}
// pure-end

function stuck(t: tm): bool
{
  normal_form(t) &&
  !value(t)
}
// pure-end

lemma corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  // pre-conditions-start
  requires has_type(map[], t) == Some(T)
  requires reduces_to(t, t', n)
  // pre-conditions-end
  // post-conditions-start
  ensures !stuck(t')
  decreases n
  // post-conditions-end
{
// impl-start
  theorem_progress(t);
  if t != t' {
    theorem_preservation(t);
    corollary_soundness(step(t).get, t', T, n - 1);
  }
// impl-end
}

datatype option<A> = None | Some(get: A)

datatype ty = TBase | TArrow(T1: ty, T2: ty)

datatype tm = tvar(id: int) | tapp(f: tm, arg: tm) | tabs(x: int, T: ty, body: tm)
