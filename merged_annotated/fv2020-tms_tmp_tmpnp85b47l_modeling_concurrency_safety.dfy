// fv2020-tms_tmp_tmpnp85b47l_modeling_concurrency_safety.dfy

method Run(processes: set<Process>)
  // pre-conditions-start
  requires processes != {}
  // pre-conditions-end
  // post-conditions-start
  decreases *
  // post-conditions-end
{
// impl-start
  var ts := new TicketSystem(processes);
  var schedule := [];
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];
  while true
    // invariants-start

    invariant ts.Valid()
    decreases *
    // invariants-end

  {
    var p :| p in ts.P;
    match ts.cs[p] {
      case {:split false} Thinking =>
        ts.Request(p);
      case {:split false} Hungry =>
        ts.Enter(p);
      case {:split false} Eating =>
        ts.Leave(p);
    }
    schedule := schedule + [p];
    trace := trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
  }
// impl-end
}

method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  // pre-conditions-start
  requires processes != {}
  requires forall n :: schedule(n) in processes
  // pre-conditions-end
  // post-conditions-start
  decreases *
  // post-conditions-end
{
// impl-start
  var ts := new TicketSystem(processes);
  var n := 0;
  while true
    // invariants-start

    invariant ts.Valid()
    decreases *
    // invariants-end

  {
    var p := schedule(n);
    match ts.cs[p] {
      case {:split false} Thinking =>
        ts.Request(p);
      case {:split false} Hungry =>
        ts.Enter(p);
      case {:split false} Eating =>
        ts.Leave(p);
    }
    n := n + 1;
  }
// impl-end
}

type Process(==) = int

datatype CState = Thinking | Hungry | Eating

class TicketSystem {
  var ticket: int
  var serving: int
  const P: set<Process>
  var cs: map<Process, CState>
  var t: map<Process, int>

  predicate Valid()
    reads this
  {
    this.cs.Keys == this.t.Keys == this.P &&
    this.serving <= this.ticket &&
    (forall p :: 
      p in this.P &&
      this.cs[p] != Thinking ==>
        this.serving <= this.t[p] < this.ticket) &&
    (forall p, q :: 
      p in this.P &&
      q in this.P &&
      p != q &&
      this.cs[p] != Thinking &&
      this.cs[q] != Thinking ==>
        this.t[p] != this.t[q]) &&
    forall p :: 
      p in this.P &&
      this.cs[p] == Eating ==>
        this.t[p] == this.serving
  }
  // pure-end

  constructor (processes: set<Process>)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.Valid()
    ensures this.P == processes
    // post-conditions-end
  {
  // impl-start
    this.P := processes;
    this.ticket, this.serving := 0, 0;
    this.cs := map p | p in processes :: Thinking;
    this.t := map p | p in processes :: 0;
  // impl-end
  }

  method Request(p: Process)
    // pre-conditions-start
    requires this.Valid() && p in this.P && this.cs[p] == Thinking
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid()
    // post-conditions-end
  {
  // impl-start
    this.t, this.ticket := this.t[p := this.ticket], this.ticket + 1;
    this.cs := this.cs[p := Hungry];
  // impl-end
  }

  method Enter(p: Process)
    // pre-conditions-start
    requires this.Valid() && p in this.P && this.cs[p] == Hungry
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid()
    // post-conditions-end
  {
  // impl-start
    if this.t[p] == this.serving {
      this.cs := this.cs[p := Eating];
    }
  // impl-end
  }

  method Leave(p: Process)
    // pre-conditions-start
    requires this.Valid() && p in this.P && this.cs[p] == Eating
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid()
    // post-conditions-end
  {
  // impl-start
    this.serving := this.serving + 1;
    this.cs := this.cs[p := Thinking];
  // impl-end
  }

  lemma MutualExclusion(p: Process, q: Process)
    // pre-conditions-start
    requires this.Valid() && p in this.P && q in this.P
    requires this.cs[p] == Eating && this.cs[q] == Eating
    // pre-conditions-end
    // post-conditions-start
    ensures p == q
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }
}
