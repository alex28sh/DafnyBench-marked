function Between(start: nat, i: nat, end: nat): bool
{
  if start < end then
    start < i < end
  else
    i < end || start < i
}
// pure-end

lemma BetweenTests()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert Between(3, 4, 5);
  assert !Between(3, 2, 4);
  assert Between(5, 2, 3);
  assert Between(5, 6, 3);
  assert !Between(5, 4, 3);
  assert forall i, k | Between(i, k, i) :: i != k;
// impl-end
}

function Init(v: Variables): bool
{
  v.UniqueIds() &&
  v.WF() &&
  forall i | v.ValidIdx(i) :: 
    v.highest_heard[i] == -1
}
// pure-end

function max(a: int, b: int): int
{
  if a > b then
    a
  else
    b
}
// pure-end

function NextIdx(v: Variables, idx: nat): nat
  requires v.WF()
  requires v.ValidIdx(idx)
{
  if idx == |v.ids| - 1 then
    0
  else
    idx + 1
}
// pure-end

function Transmission(v: Variables, v': Variables, step: Step): bool
  requires step.TransmissionStep?
{
  var src := step.src;
  v.WF() &&
  v.ValidIdx(src) &&
  v'.ids == v.ids &&
  var dst := NextIdx(v, src); true && var message := max(v.highest_heard[src], v.ids[src]); true && var dst_new_max := max(v.highest_heard[dst], message); true && v'.highest_heard == v.highest_heard[dst := dst_new_max]
}
// pure-end

function NextStep(v: Variables, v': Variables, step: Step): bool
{
  match step {
    case TransmissionStep(_ /* _v0 */) =>
      Transmission(v, v', step)
  }
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

function Next(v: Variables, v': Variables): bool
{
  exists step :: 
    NextStep(v, v', step)
}
// pure-end

function IsLeader(v: Variables, i: int): bool
  requires v.WF()
{
  v.ValidIdx(i) &&
  v.highest_heard[i] == v.ids[i]
}
// pure-end

function Safety(v: Variables): bool
  requires v.WF()
{
  forall i, j | IsLeader(v, i) && IsLeader(v, j) :: 
    i == j
}
// pure-end

function ChordHeardDominated(v: Variables, start: nat, end: nat): bool
  requires v.IsChord(start, end)
  requires v.WF()
{
  forall i | v.ValidIdx(i) && Between(start, i, end) :: 
    v.highest_heard[i] > v.ids[i]
}
// pure-end

function {:opaque} OnChordHeardDominatesId(v: Variables): bool
  requires v.WF()
{
  forall start: nat, end: nat | v.IsChord(start, end) :: 
    ChordHeardDominated(v, start, end)
}
// pure-end

lemma UseChordDominated(v: Variables, start: nat, end: nat)
  // pre-conditions-start
  requires v.WF()
  requires OnChordHeardDominatesId(v)
  requires v.IsChord(start, end)
  // pre-conditions-end
  // post-conditions-start
  ensures ChordHeardDominated(v, start, end)
  // post-conditions-end
{
// impl-start
  reveal OnChordHeardDominatesId();
// impl-end
}

function Inv(v: Variables): bool
{
  v.WF() &&
  v.UniqueIds() &&
  OnChordHeardDominatesId(v)
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
  forall start: nat, end: nat | v.IsChord(start, end)
    ensures false
  {
  }
  assert OnChordHeardDominatesId(v) by {
    reveal OnChordHeardDominatesId();
  }
// impl-end
}

lemma NextPreservesInv(v: Variables, v': Variables)
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
  var src := step.src;
  var dst := NextIdx(v, src);
  var message := max(v.highest_heard[src], v.ids[src]);
  var dst_new_max := max(v.highest_heard[dst], message);
  assert v'.UniqueIds();
  forall start: nat, end: nat | v'.IsChord(start, end)
    ensures ChordHeardDominated(v', start, end)
  {
    if dst == end {
      if dst_new_max == v.highest_heard[dst] {
        assert v' == v;
        UseChordDominated(v, start, end);
        assert ChordHeardDominated(v', start, end);
      } else if v'.highest_heard[dst] == v.ids[src] {
        assert start == src;
        assert forall k | v.ValidIdx(k) :: !Between(start, k, end);
        assert ChordHeardDominated(v', start, end);
      } else if v'.highest_heard[end] == v.highest_heard[src] {
        assert v.IsChord(start, src);
        UseChordDominated(v, start, src);
        assert ChordHeardDominated(v', start, end);
      }
      assert ChordHeardDominated(v', start, end);
    } else {
      assert v.IsChord(start, end);
      UseChordDominated(v, start, end);
      assert ChordHeardDominated(v', start, end);
    }
  }
  assert OnChordHeardDominatesId(v') by {
    reveal OnChordHeardDominatesId();
  }
// impl-end
}

lemma InvImpliesSafety(v: Variables)
  // pre-conditions-start
  requires Inv(v)
  // pre-conditions-end
  // post-conditions-start
  ensures Safety(v)
  // post-conditions-end
{
// impl-start
  forall i: nat, j: nat | IsLeader(v, i) && IsLeader(v, j)
    ensures i == j
  {
    assert forall k | v.ValidIdx(k) && Between(i, k, i) :: i != k;
    assert v.highest_heard[j] == v.ids[j];
    if i != j {
      assert v.IsChord(i, i);
      assert Between(i, j, i);
      UseChordDominated(v, i, i);
      assert false;
    }
  }
// impl-end
}

datatype Variables = Variables(ids: seq<nat>, highest_heard: seq<int>) {
  function ValidIdx(i: int): bool
  {
    0 <= i < |ids|
  }
// pure-end

  function UniqueIds(): bool
  {
    forall i, j | ValidIdx(i) && ValidIdx(j) :: 
      ids[i] == ids[j] ==>
        i == j
  }
// pure-end

  function WF(): bool
  {
    0 < |ids| &&
    |ids| == |highest_heard|
  }
// pure-end

  function IsChord(start: nat, end: nat): bool
  {
    ValidIdx(start) &&
    ValidIdx(end) &&
    WF() &&
    highest_heard[end] == ids[start]
  }
// pure-end
}

datatype Step = TransmissionStep(src: nat)
