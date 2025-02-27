// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var left: Node?
  var right: Node?
  var parent: Node?
  var anc: set<Node>
  var desc: set<Node>
  var sense: bool
  var pc: int

  predicate validDown()
    reads this, this.desc
  {
    this !in this.desc &&
    this.left != this.right &&  // not needed, but speeds up verification

    (this.right != null ==> this.right in this.desc && this.left !in this.right.desc) &&

    (this.left != null ==>
      this.left in this.desc &&
      (this.right != null ==> this.desc == {this.left, this.right} + this.left.desc + this.right.desc)  &&
      (this.right == null ==> this.desc == {this.left} + this.left.desc)  &&
      this.left.validDown()) &&
    (this.left == null ==>
      (this.right != null ==> this.desc == {this.right} + this.right.desc)  &&
      (this.right == null ==> this.desc == {})) &&

    (this.right != null ==> this.right.validDown()) &&

    (this.blocked() ==> forall m :: m in this.desc ==> m.blocked()) &&
    (this.after() ==> forall m :: m in this.desc ==> m.blocked() || m.after())
//    (left != null && right != null ==> left.desc !! right.desc)  // not needed
  }

  predicate validUp()
    reads this, this.anc
  {
    this !in this.anc &&
    (this.parent != null ==> this.parent in this.anc && this.anc == { this.parent } + this.parent.anc && this.parent.validUp()) &&
    (this.parent == null ==> this.anc == {}) &&
    (this.after() ==> forall m :: m in this.anc ==> m.after())
  }

  predicate valid()
    reads this, this.desc, this.anc
  { this.validUp() && this.validDown() && this.desc !! this.anc }

  predicate before()
    reads this
  { !this.sense && this.pc <= 2 }

  predicate blocked()
    reads this
  { this.sense }

  predicate after()
    reads this
  { !this.sense && 3 <= this.pc }

  method barrier()
    requires this.valid()
    requires this.before()
    modifies this, this.left, this.right
    decreases *  // allow the method to not terminate
  {
//A
    this.pc := 1;
    if(this.left != null) {
      while(!this.left.sense)
        modifies this.left
        invariant this.validDown() // this seems necessary to get the necessary unfolding of functions
        invariant this.valid()
        decreases *  // to by-pass termination checking for this loop
      {
        // this loop body is supposed to model what the "left" thread
        // might do to its node. This body models a transition from
        // "before" to "blocked" by setting sense to true. A transition
        // all the way to "after" is not permitted; this would require
        // a change of pc.
        // We assume that "left" preserves the validity of its subtree,
        // which means in particular that it goes to "blocked" only if
        // all its descendants are already blocked.
        this.left.sense := *;
        assume this.left.blocked() ==> forall m :: m in this.left.desc ==> m.blocked();
      }
    }
    if(this.right != null) {
      while(!this.right.sense)
        modifies this.right
        invariant this.validDown() // this seems necessary to get the necessary unfolding of functions
        invariant this.valid()
        decreases *  // to by-pass termination checking for this loop
      {
        // analogous to the previous loop
        this.right.sense := *;
        assume this.right.blocked() ==> forall m :: m in this.right.desc ==> m.blocked();
      }
    }

//B
    this.pc := 2;
    if(this.parent != null) {
      this.sense := true;
    }
//C
    this.pc := 3;
    while(this.sense)
        modifies this
        invariant this.validUp() // this seems necessary to get the necessary unfolding of functions
        invariant this.valid()
        invariant this.left == old(this.left)
        invariant this.right == old(this.right)
        invariant this.sense ==> this.parent != null
        decreases *  // to by-pass termination checking for this loop
    {
      // this loop body is supposed to model what the "parent" thread
      // might do to its node. The body models a transition from
      // "blocked" to "after" by setting sense to false.
      // We assume that "parent" initiates this transition only
      // after it went to state "after" itself.
      this.sense := *;
      assume !this.sense ==> this.parent.after();
    }
//D
    this.pc := 4;
    if(this.left != null) {
      this.left.sense := false;
    }
//E
    this.pc := 5;
    if(this.right != null) {
      this.right.sense := false;
    }
//F
    this.pc := 6;
  }
}
