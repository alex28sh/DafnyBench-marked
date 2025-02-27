// dafny-language-server_tmp_tmpkir0kenl_Test_dafny2_TreeBarrier.dfy

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
    this.left != this.right &&
    (this.right != null ==>
      this.right in this.desc &&
      this.left !in this.right.desc) &&
    (this.left != null ==>
      this.left in this.desc &&
      (this.right != null ==>
        this.desc == {this.left, this.right} + this.left.desc + this.right.desc) &&
      (this.right == null ==>
        this.desc == {this.left} + this.left.desc) &&
      this.left.validDown()) &&
    (this.left == null ==>
      (this.right != null ==>
        this.desc == {this.right} + this.right.desc) &&
      (this.right == null ==>
        this.desc == {})) &&
    (this.right != null ==>
      this.right.validDown()) &&
    (this.blocked() ==>
      forall m :: 
        m in this.desc ==>
          m.blocked()) &&
    (this.after() ==>
      forall m :: 
        m in this.desc ==>
          m.blocked() || m.after())
  }
  // pure-end

  predicate validUp()
    reads this, this.anc
  {
    this !in this.anc &&
    (this.parent != null ==>
      this.parent in this.anc &&
      this.anc == {this.parent} + this.parent.anc &&
      this.parent.validUp()) &&
    (this.parent == null ==>
      this.anc == {}) &&
    (this.after() ==>
      forall m :: 
        m in this.anc ==>
          m.after())
  }
  // pure-end

  predicate valid()
    reads this, this.desc, this.anc
  {
    this.validUp() &&
    this.validDown() &&
    this.desc !! this.anc
  }
  // pure-end

  predicate before()
    reads this
  {
    !this.sense &&
    this.pc <= 2
  }
  // pure-end

  predicate blocked()
    reads this
  {
    this.sense
  }
  // pure-end

  predicate after()
    reads this
  {
    !this.sense &&
    3 <= this.pc
  }
  // pure-end

  method barrier()
    // pre-conditions-start
    requires this.valid()
    requires this.before()
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.left, this.right
    decreases *
    // post-conditions-end
  {
  // impl-start
    this.pc := 1;
    if this.left != null {
      while !this.left.sense
        // invariants-start

        invariant this.validDown()
        invariant this.valid()
        decreases *
        modifies this.left
        // invariants-end

      {
        this.left.sense := *;
        // assert-start
        assume this.left.blocked() ==> forall m :: m in this.left.desc ==> m.blocked();
        // assert-end

      }
    }
    if this.right != null {
      while !this.right.sense
        // invariants-start

        invariant this.validDown()
        invariant this.valid()
        decreases *
        modifies this.right
        // invariants-end

      {
        this.right.sense := *;
        // assert-start
        assume this.right.blocked() ==> forall m :: m in this.right.desc ==> m.blocked();
        // assert-end

      }
    }
    this.pc := 2;
    if this.parent != null {
      this.sense := true;
    }
    this.pc := 3;
    while this.sense
      // invariants-start

      invariant this.validUp()
      invariant this.valid()
      invariant this.left == old(this.left)
      invariant this.right == old(this.right)
      invariant this.sense ==> this.parent != null
      decreases *
      modifies this
      // invariants-end

    {
      this.sense := *;
      // assert-start
      assume !this.sense ==> this.parent.after();
      // assert-end

    }
    this.pc := 4;
    if this.left != null {
      this.left.sense := false;
    }
    this.pc := 5;
    if this.right != null {
      this.right.sense := false;
    }
    this.pc := 6;
  // impl-end
  }
}
