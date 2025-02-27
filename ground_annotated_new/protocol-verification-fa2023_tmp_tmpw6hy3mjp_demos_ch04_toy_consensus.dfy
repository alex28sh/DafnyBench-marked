
ghost predicate Member(n: Node, q: Quorum)
// pure-end

lemma {:axiom} QuorumIntersect(q1: Quorum, q2: Quorum) returns (n: Node)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Member(n, q1) && Member(n, q2)
  // post-conditions-end

ghost predicate CastVote(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.CastVoteStep?
{
  var n := step.n;
  v.votes[n] == {} &&
  v' == v.(votes := v.votes[n := v.votes[n] + {step.c}])
}
// pure-end

ghost predicate Decide(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.DecideStep?
{
  (forall n: Node | Member(n, step.q) :: 
    step.c in v.votes[n]) &&
  v' == v.(decision := v.decision + {step.c})
}
// pure-end

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  v.WF() &&
  match step { case CastVoteStep(_ /* _v0 */, _ /* _v1 */) => CastVote(v, v', step) case DecideStep(_ /* _v2 */, _ /* _v3 */) => Decide(v, v', step) }
}
// pure-end

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  // pre-conditions-start
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  // pre-conditions-end
  // post-conditions-start
  ensures v'1 == v'2
  // post-conditions-end
{
// impl-start
// impl-end
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: 
    NextStep(v, v', step)
}
// pure-end

ghost predicate Init(v: Variables)
{
  v.WF() &&
  (forall n :: 
    v.votes[n] == {}) &&
  v.decision == {}
}
// pure-end

ghost predicate Safety(v: Variables)
{
  forall c1, c2 :: 
    c1 in v.decision &&
    c2 in v.decision ==>
      c1 == c2
}
// pure-end

ghost predicate ChoiceQuorum(v: Variables, q: Quorum, c: Choice)
  requires v.WF()
{
  forall n :: 
    Member(n, q) ==>
      c in v.votes[n]
}
// pure-end

ghost predicate Inv(v: Variables)
{
  v.WF() &&
  Safety(v) &&
  (forall n, v1, v2 :: 
    v1 in v.votes[n] &&
    v2 in v.votes[n] ==>
      v1 == v2) &&
  forall c :: 
    c in v.decision ==>
      exists q: Quorum :: 
        ChoiceQuorum(v, q, c)
}
// pure-end

lemma InitImpliesInv(v: Variables)
  // pre-conditions-start
  requires Init(v)
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(v)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma InvInductive(v: Variables, v': Variables)
  // pre-conditions-start
  requires Inv(v)
  requires Next(v, v')
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(v')
  // post-conditions-end
{
// impl-start
  var step :| NextStep(v, v', step);
  match step {
    case {:split false} CastVoteStep(n, c) =>
      {
        forall c | c in v'.decision
          ensures exists q: Quorum :: ChoiceQuorum(v', q, c)
        {
          var q :| ChoiceQuorum(v, q, c);
          assert ChoiceQuorum(v', q, c);
        }
        return;
      }
    case {:split false} DecideStep(c, q) =>
      {
        forall c | c in v'.decision
          ensures exists q: Quorum :: ChoiceQuorum(v', q, c)
        {
          var q0 :| ChoiceQuorum(v, q0, c);
          assert ChoiceQuorum(v', q0, c);
        }
        forall c1, c2 | c1 in v'.decision && c2 in v'.decision
          ensures c1 == c2
        {
          var q1 :| ChoiceQuorum(v, q1, c1);
          var q2 :| ChoiceQuorum(v, q2, c2);
          var n := QuorumIntersect(q1, q2);
        }
        assert Safety(v');
        return;
      }
  }
// impl-end
}

lemma SafetyHolds(v: Variables, v': Variables)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
  // post-conditions-end
{
// impl-start
  if Inv(v) && Next(v, v') {
    InvInductive(v, v');
  }
// impl-end
}

type Node(==,!new)

type Quorum(==,!new)

type Choice(==,!new)

datatype Variables = Variables(votes: map<Node, set<Choice>>, decision: set<Choice>) {
  ghost predicate WF()
  {
    true &&
    forall n: Node :: 
      n in votes
  }
  // pure-end
}

datatype Step = CastVoteStep(n: Node, c: Choice) | DecideStep(c: Choice, q: Quorum)
