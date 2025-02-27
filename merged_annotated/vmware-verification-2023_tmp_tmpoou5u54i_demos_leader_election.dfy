
ghost predicate Init(c: Constants, v: Variables)
{
  v.WF(c) &&
  c.UniqueIds() &&
  forall i | c.ValidIdx(i) :: 
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

function NextIdx(c: Constants, idx: nat): nat
  requires c.WF()
  requires c.ValidIdx(idx)
{
  if idx + 1 == |c.ids| then
    0
  else
    idx + 1
}
// pure-end

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat)
{
  v.WF(c) &&
  v'.WF(c) &&
  c.ValidIdx(srcidx) &&
  var dstidx := NextIdx(c, srcidx); true && var message := max(v.highest_heard[srcidx], c.ids[srcidx]); true && var dst_new_max := max(v.highest_heard[dstidx], message); true && v' == v.(highest_heard := v.highest_heard[dstidx := dst_new_max])
}
// pure-end

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(srcidx) =>
      Transmission(c, v, v', srcidx)
  }
}
// pure-end

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  exists step :: 
    NextStep(c, v, v', step)
}
// pure-end

ghost predicate IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c)
{
  c.ValidIdx(i) &&
  v.highest_heard[i] == c.ids[i]
}
// pure-end

ghost predicate Safety(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: 
    i == j
}
// pure-end

ghost predicate IsChord(c: Constants, v: Variables, start: int, end: int)
{
  v.WF(c) &&
  c.ValidIdx(start) &&
  c.ValidIdx(end) &&
  c.ids[start] == v.highest_heard[end]
}
// pure-end

ghost predicate Between(start: int, node: int, end: int)
{
  if start < end then
    start < node < end
  else
    node < end || start < node
}
// pure-end

ghost predicate OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c)
{
  forall node | Between(start, node, end) && c.ValidIdx(node) :: 
    v.highest_heard[node] > c.ids[node]
}
// pure-end

ghost predicate OnChordHeardDominatesIdInv(c: Constants, v: Variables)
{
  v.WF(c) &&
  forall start, end | IsChord(c, v, start, end) :: 
    OnChordHeardDominatesId(c, v, start, end)
}
// pure-end

ghost predicate Inv(c: Constants, v: Variables)
{
  v.WF(c) &&
  OnChordHeardDominatesIdInv(c, v) &&
  Safety(c, v)
}
// pure-end

lemma InitImpliesInv(c: Constants, v: Variables)
  // pre-conditions-start
  requires Init(c, v)
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(c, v)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  // pre-conditions-start
  requires Inv(c, v)
  requires Next(c, v, v')
  // pre-conditions-end
  // post-conditions-start
  ensures Inv(c, v')
  // post-conditions-end
{
// impl-start
  var step :| NextStep(c, v, v', step);
  var srcidx := step.srcidx;
  var dstidx := NextIdx(c, srcidx);
  var message := max(v.highest_heard[srcidx], c.ids[srcidx]);
  var dst_new_max := max(v.highest_heard[dstidx], message);
  forall start, end | IsChord(c, v', start, end)
    ensures OnChordHeardDominatesId(c, v', start, end)
  {
    forall node | Between(start, node, end) && c.ValidIdx(node)
      ensures v'.highest_heard[node] > c.ids[node]
    {
      if dstidx == end {
        if v'.highest_heard[end] == v.highest_heard[end] {
          assert v' == v;
        } else if v'.highest_heard[end] == c.ids[srcidx] {
          assert false;
        } else if v'.highest_heard[end] == v.highest_heard[srcidx] {
          assert IsChord(c, v, start, srcidx);
        }
      } else {
        assert IsChord(c, v, start, end);
      }
    }
  }
  assert OnChordHeardDominatesIdInv(c, v');
  forall i, j | IsLeader(c, v', i) && IsLeader(c, v', j)
    ensures i == j
  {
    assert IsChord(c, v', i, i);
    assert IsChord(c, v', j, j);
  }
  assert Safety(c, v');
// impl-end
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  // pre-conditions-start
  requires Inv(c, v)
  // pre-conditions-end
  // post-conditions-start
  ensures Safety(c, v)
  // post-conditions-end
{
// impl-start
// impl-end
}

datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: int)
  {
    0 <= i < |ids|
  }
  // pure-end

  ghost predicate UniqueIds()
  {
    forall i, j | ValidIdx(i) && ValidIdx(j) && ids[i] == ids[j] :: 
      i == j
  }
  // pure-end

  ghost predicate WF()
  {
    0 < |ids| &&
    UniqueIds()
  }
  // pure-end
}

datatype Variables = Variables(highest_heard: seq<int>) {
  ghost predicate WF(c: Constants)
  {
    c.WF() &&
    |highest_heard| == |c.ids|
  }
  // pure-end
}

datatype Step = TransmissionStep(srcidx: nat)
