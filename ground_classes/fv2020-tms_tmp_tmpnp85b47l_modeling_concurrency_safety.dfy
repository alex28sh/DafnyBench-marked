/*
 * Model of the ticket system and correctness theorem
 * Parts 4 and 5 in the paper
 */
type Process(==) = int  // Philosopher

datatype CState = Thinking | Hungry | Eating  // Control states

// A class can have state, with multiple fields, methods, a constructor, and declare functions and lemmas
class TicketSystem
{
  var ticket: int  // Ticket dispenser
  var serving: int  // Serving display

  const P: set<Process>  // Fixed set of processes

  // State for each process
  var cs: map<Process, CState>  // (Partial) Map from process to state
  var t: map<Process, int>  // (Partial) Map from process to ticket number

  // Invariant of the system
  // Checks that P is a subset of the domain/keys of each map
  predicate Valid()
    reads this  // Depends on the fields on the current class
  {
    && this.cs.Keys == this.t.Keys == this.P  // Alt. P <= cs.Keys && P <= t.Keys
    && this.serving <= this.ticket
    && (forall p ::  // ticket help is in range(serving, ticket)
      p in this.P && this.cs[p] != Thinking
      ==> this.serving <= this.t[p] < this.ticket
    )
    && (forall p, q ::  // No other process can have the ticket number equals to serving
      p in this.P && q in this.P && p != q && this.cs[p] != Thinking && this.cs[q] != Thinking
      ==> this.t[p] != this.t[q]
    )
    && (forall p ::  // We are serving the correct ticket number
      p in this.P && this.cs[p] == Eating
      ==> this.t[p] == this.serving
    )
  }

  // Initialize the ticket system
  constructor (processes: set<Process>)
    ensures this.Valid()  // Postcondition
    ensures this.P == processes  // Connection between processes and ts.P
  {
    this.P := processes;
    this.ticket, this.serving := 0, 0;  // Alt. ticket := serving;
    // The two following use map comprehension
    this.cs := map p | p in processes :: Thinking;  // The map from p, where p in processes, takes value Thinking
    this.t := map p | p in processes :: 0;
  }

  // The next three methods are our atomic events
  // A Philosopher is Thinking and gets Hungry
  method Request(p: Process)
    requires this.Valid() && p in this.P && this.cs[p] == Thinking  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures this.Valid()  // Postcondition
  {
    this.t, this.ticket := this.t[p := this.ticket], this.ticket + 1;  // Philosopher gets current ticket, next ticket's number increases
    this.cs := this.cs[p := Hungry];  // Philosopher's state changes to Hungry
  }

  // A Philosopher is Hungry and enters the kitchen
  method Enter(p: Process)
    requires this.Valid() && p in this.P && this.cs[p] == Hungry  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures this.Valid()  // Postcondition
  {
    if this.t[p] == this.serving  // The kitchen is available for this Philosopher
    {
      this.cs := this.cs[p := Eating];  // Philosopher's state changes to Eating
    }
  }

  // A Philosopher is done Eating and leaves the kitchen
  method Leave(p: Process)
    requires this.Valid() && p in this.P && this.cs[p] == Eating  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures this.Valid()  // Postcondition
  {
    //assert this.t[p] == this.serving;  // Ticket held by p is equal to serving
    this.serving := this.serving + 1;  // Kitchen is ready to serve the next ticket holder
    this.cs := this.cs[p := Thinking];  // Philosopher's state changes to Thinking
  }

  // Ensures that no two processes are in the same state
  lemma MutualExclusion(p: Process, q: Process)
    // Antecedents
    requires this.Valid() && p in this.P && q in this.P
    requires this.cs[p] == Eating && this.cs[q] == Eating
    // Conclusion/Proof goal
    ensures p == q
  {

  }
}

/*
 * Event scheduler
 * Part 6 in the paper
 * Part 6.1 for alternatives
 */
method Run(processes: set<Process>)
  requires processes != {}  // Cannot schedule no processes
  decreases *  // Needed so that the loop omits termination checks
{
  var ts := new TicketSystem(processes);
  var schedule := [];  // Scheduling choices
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];  // Record sequence of states
  
  while true
    invariant ts.Valid()
    decreases *  // Omits termination checks
  {
    var p :| p in ts.P;  // p exists such that p is in ts.P
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    schedule := schedule + [p];
    trace := trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
  }
}

/*
 * Event scheduler with planified schedule
 * Part 6.2
 */
method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  requires processes != {}
  requires forall n :: schedule(n) in processes
  decreases *
{
  var ts := new TicketSystem(processes);
  var n := 0;
  
  while true
    invariant ts.Valid()
    decreases *  // Omits termination checks
  {
    var p := schedule(n);
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    n := n + 1;
  }
}
