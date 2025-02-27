// protocol-verification-fa2023_tmp_tmpw6hy3mjp_demos_ch06_refinement_proof.dfy

ghost predicate Inv(v: Code.Variables)
// pure-end

ghost function Abstraction(v: Code.Variables): Spec.Variables
// pure-end

lemma {:axiom} AbstractionInit(v: Code.Variables)
  // pre-conditions-start
  requires Code.Init(v)
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(v)
  ensures Spec.Init(Abstraction(v))
  // post-conditions-end

lemma {:axiom} AbstractionInductive(v: Code.Variables, v': Code.Variables, ev: Event)
  // pre-conditions-start
  requires Inv(v)
  requires Code.Next(v, v', ev)
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(v')
  ensures Spec.Next(Abstraction(v), Abstraction(v'), ev)
  // post-conditions-end

lemma InvAt(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  // pre-conditions-start
  requires Code.Init(ss(0))
  requires forall k: nat :: Code.Next(ss(k), ss(k + 1), tr(k))
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(ss(i))
  // post-conditions-end
{
// impl-start
  if i == 0 {
    AbstractionInit(ss(0));
  } else {
    InvAt(tr, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), tr(i - 1));
  }
// impl-end
}

lemma RefinementTo(tr: nat -> Event, ss: nat -> Code.Variables, i: nat)
  // pre-conditions-start
  requires forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n))
  requires forall n: nat :: Inv(ss(n))
  // pre-conditions-end
  // post-conditions-start
  ensures var ss' := (j: nat) => Abstraction(ss(j)); true && forall n: nat | n < i :: Spec.Next(ss'(n), ss'(n + 1), tr(n))
  // post-conditions-end
{
// impl-start
  if i == 0 {
    return;
  } else {
    var ss' := (j: nat) => Abstraction(ss(j));
    RefinementTo(tr, ss, i - 1);
    AbstractionInductive(ss(i - 1), ss(i), tr(i - 1));
  }
// impl-end
}

lemma Refinement(tr: nat -> Event)
  // pre-conditions-start
  requires Code.IsBehavior(tr)
  // pre-conditions-end
  // post-conditions-start
  ensures Spec.IsBehavior(tr)
  // post-conditions-end
{
// impl-start
  var ss: nat -> Code.Variables :| Code.Init(ss(0)) && forall n: nat :: Code.Next(ss(n), ss(n + 1), tr(n));
  forall i: nat | true
    ensures Inv(ss(i))
  {
    InvAt(tr, ss, i);
  }
  var ss': nat -> Spec.Variables := (i: nat) => Abstraction(ss(i));
  assert Spec.Init(ss'(0)) by {
    AbstractionInit(ss(0));
  }
  forall n: nat | true
    ensures Spec.Next(ss'(n), ss'(n + 1), tr(n))
  {
    RefinementTo(tr, ss, n + 1);
  }
// impl-end
}

module Types {
  type Event(==,0,!new)
}

import opened Types

module Code {
  ghost predicate Init(v: Variables)
  // pure-end

  ghost predicate Next(v: Variables, v': Variables, ev: Event)
  // pure-end

  ghost predicate IsBehavior(tr: nat -> Event)
  {
    exists ss: nat -> Variables :: 
      Init(ss(0)) &&
      forall n: nat :: 
        Next(ss(n), ss(n + 1), tr(n))
  }
  // pure-end

  import opened Types

  type Variables(==,0,!new)
}

module Spec {
  ghost predicate Init(v: Variables)
  // pure-end

  ghost predicate Next(v: Variables, v': Variables, ev: Event)
  // pure-end

  ghost predicate IsBehavior(tr: nat -> Event)
  {
    exists ss: nat -> Variables :: 
      Init(ss(0)) &&
      forall n: nat :: 
        Next(ss(n), ss(n + 1), tr(n))
  }
  // pure-end

  import opened Types

  type Variables(==,0,!new)
}
