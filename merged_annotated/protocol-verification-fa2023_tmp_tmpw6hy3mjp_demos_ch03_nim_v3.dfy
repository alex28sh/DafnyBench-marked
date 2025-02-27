
ghost predicate Init(v: Variables)
{
  |v.piles| == 3 &&
  v.turn.P1?
}
// pure-end

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
{
  var p := step.p;
  var take := step.take;
  p < |v.piles| &&
  take <= v.piles[p] &&
  v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
}
// pure-end

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case TurnStep(_ /* _v0 */, _ /* _v1 */) =>
      Turn(v, v', step)
    case NoOpStep() =>
      v' == v
  }
}
// pure-end

lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  // pre-conditions-start
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  // pre-conditions-end
  // post-conditions-start
  ensures v' == v''
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

lemma ExampleBehavior() returns (b: seq<Variables>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |b| >= 3
  ensures Init(b[0])
  ensures forall i: nat | i + 1 < |b| :: Next(b[i], b[i + 1])
  // post-conditions-end
{
// impl-start
  var state0 := Variables(piles := [3, 5, 7], turn := P1);
  b := [state0, Variables(piles := [3, 1, 7], turn := P2), Variables(piles := [3, 1, 0], turn := P1)];
  assert NextStep(b[0], b[1], TurnStep(take := 4, p := 1));
  assert NextStep(b[1], b[2], TurnStep(take := 7, p := 2));
// impl-end
}

datatype Player = P1 | P2 {
  function Other(): Player
  {
    if this == P1 then
      P2
    else
      P1
  }
  // pure-end
}

datatype Variables = Variables(piles: seq<nat>, turn: Player)

datatype Step = TurnStep(take: nat, p: nat) | NoOpStep
