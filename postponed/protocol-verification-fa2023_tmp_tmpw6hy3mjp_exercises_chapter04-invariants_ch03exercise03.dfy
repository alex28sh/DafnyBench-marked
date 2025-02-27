
ghost predicate Init(v: Variables)
{
  v.WellFormed() &&
  v.server.Unlocked? &&
  |v.clients| == v.clientCount &&
  forall i | 0 <= i < |v.clients| :: 
    v.clients[i].Released?
}
// pure-end

ghost predicate Acquire(v: Variables, v': Variables, id: int)
{
  v.WellFormed() &&
  v'.WellFormed() &&
  v.ValidIdx(id) &&
  v.server.Unlocked? &&
  v'.server == Client(id) &&
  v'.clients == v.clients[id := Acquired] &&
  v'.clientCount == v.clientCount
}
// pure-end

ghost predicate Release(v: Variables, v': Variables, id: int)
{
  v.WellFormed() &&
  v'.WellFormed() &&
  v.ValidIdx(id) &&
  v.clients[id].Acquired? &&
  v'.server.Unlocked? &&
  v'.clients == v.clients[id := Released] &&
  v'.clientCount == v.clientCount
}
// pure-end

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step
  case AcquireStep(id) =>
    Acquire(v, v', id)
  case ReleaseStep(id) =>
    Release(v, v', id)
}
// pure-end

lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, step: Step)
  // pre-conditions-start
  requires NextStep(v, v', step)
  // pre-conditions-end
  // post-conditions-start
  ensures forall v'' | NextStep(v, v'', step) :: v' == v''
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

ghost predicate Safety(v: Variables)
{
  forall i, j | 0 <= i < |v.clients| && 0 <= j < |v.clients| && v.clients[i].Acquired? && v.clients[j].Acquired? :: 
    i == j
}
// pure-end

ghost predicate ClientHoldsLock(v: Variables, clientIndex: nat)
  requires v.WellFormed()
{
  true &&
  v.server == Client(clientIndex)
}
// pure-end

lemma PseudoLiveness(clientA: nat, clientB: nat) returns (behavior: seq<Variables>)
  // pre-conditions-start
  requires clientA == 2
  requires clientB == 0
  // pre-conditions-end
  // post-conditions-start
  ensures 2 <= |behavior|
  ensures Init(behavior[0])
  ensures forall i | 0 <= i < |behavior| - 1 :: Next(behavior[i], behavior[i + 1])
  ensures forall i | 0 <= i < |behavior| :: Safety(behavior[i])
  ensures behavior[|behavior| - 1].WellFormed()
  ensures ClientHoldsLock(behavior[1], clientA)
  ensures ClientHoldsLock(behavior[|behavior| - 1], clientB)
  // post-conditions-end
{
// impl-start
  var state0 := Variables(clientCount := 3, server := Unlocked, clients := [Released, Released, Released]);
  var state1 := Variables(clientCount := 3, server := Client(clientA), clients := [Released, Released, Acquired]);
  var state2 := Variables(clientCount := 3, server := Unlocked, clients := [Released, Released, Released]);
  var state3 := Variables(clientCount := 3, server := Client(clientB), clients := [Acquired, Released, Released]);
  assert NextStep(state0, state1, AcquireStep(clientA));
  assert Release(state1, state2, 2);
  assert NextStep(state1, state2, ReleaseStep(clientA));
  assert NextStep(state2, state3, AcquireStep(clientB));
  behavior := [state0, state1, state2, state3];
// impl-end
}

datatype ServerGrant = Unlocked | Client(id: nat)

datatype ClientRecord = Released | Acquired

datatype Variables = Variables(clientCount: nat, server: ServerGrant, clients: seq<ClientRecord>) {
  ghost predicate ValidIdx(idx: int)
  {
    0 <= idx < this.clientCount
  }
  // pure-end

  ghost predicate WellFormed()
  {
    |clients| == this.clientCount
  }
  // pure-end
}

datatype Step = AcquireStep(id: int) | ReleaseStep(id: int)
