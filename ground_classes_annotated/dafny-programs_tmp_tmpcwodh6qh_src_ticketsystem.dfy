// dafny-programs_tmp_tmpcwodh6qh_src_ticketsystem.dfy

type Process(==,!new)

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
    this.P <= this.cs.Keys &&
    this.P <= this.t.Keys &&
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
    // assert-start
    assert this.t[p] == this.serving;
    // assert-end

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
}
