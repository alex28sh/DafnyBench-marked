// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Composite {
  var left: Composite?
  var right: Composite?
  var parent: Composite?
  var val: int
  var sum: int

  function Valid(S: set<Composite>): bool
    reads this, this.parent, this.left, this.right
  {
    this in S &&
    (this.parent != null ==> this.parent in S && (this.parent.left == this || this.parent.right == this)) &&
    (this.left != null ==> this.left in S && this.left.parent == this && this.left != this.right) &&
    (this.right != null ==> this.right in S && this.right.parent == this && this.left != this.right) &&
    this.sum == this.val + (if this.left == null then 0 else this.left.sum) + (if this.right == null then 0 else this.right.sum)
  }

  function Acyclic(S: set<Composite>): bool
    reads S
  {
    this in S &&
    (this.parent != null ==> this.parent.Acyclic(S - {this}))
  }

  method Init(x: int)
    modifies this
    ensures this.Valid({this}) && this.Acyclic({this}) && this.val == x && this.parent == null
  {
    this.parent := null;
    this.left := null;
    this.right := null;
    this.val := x;
    this.sum := this.val;
  }

  method Update(x: int, ghost S: set<Composite>)
    requires this in S && this.Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c :: c in S ==> c.Valid(S)
    ensures forall c :: c in S ==> c.left == old(c.left) && c.right == old(c.right) && c.parent == old(c.parent)
    ensures forall c :: c in S && c != this ==> c.val == old(c.val)
    ensures this.val == x
  {
    var delta := x - this.val;
    this.val := x;
    this.Adjust(delta, S, S);
  }

  method Add(ghost S: set<Composite>, child: Composite, ghost U: set<Composite>)
    requires this in S && this.Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    requires child in U
    requires forall c :: c in U ==> c.Valid(U)
    requires S !! U
    requires this.left == null || this.right == null
    requires child.parent == null
    // modifies only one of this.left and this.right, and child.parent, and various sum fields:
    modifies S, child
    ensures child.left == old(child.left) && child.right == old(child.right) && child.val == old(child.val)
    ensures forall c :: c in S && c != this ==> c.left == old(c.left) && c.right == old(c.right)
    ensures old(this.left) != null ==> this.left == old(this.left)
    ensures old(this.right) != null ==> this.right == old(this.right)
    ensures forall c :: c in S ==> c.parent == old(c.parent) && c.val == old(c.val)
    // sets child.parent to this:
    ensures child.parent == this
    // leaves everything in S+U valid
    ensures forall c: Composite {:autotriggers false} :: c in S+U ==> c.Valid(S+U) // We can't generate a trigger for this at the moment; if we did, we would still need to prevent TrSplitExpr from translating c in S+U to S[c] || U[c].
  {
    if (this.left == null) {
      this.left := child;
    } else {
      this.right := child;
    }
    child.parent := this;
    this.Adjust(child.sum, S, S+U);
  }

  method Dislodge(ghost S: set<Composite>)
    requires this in S && this.Acyclic(S)
    requires forall c :: c in S ==> c.Valid(S)
    modifies S
    ensures forall c :: c in S ==> c.Valid(S)
    ensures forall c :: c in S ==> c.val == old(c.val)
    ensures forall c :: c in S && c != this ==> c.parent == old(c.parent)
    ensures this.parent == null
    ensures forall c :: c in S ==> c.left == old(c.left) || (old(c.left) == this && c.left == null)
    ensures forall c :: c in S ==> c.right == old(c.right) || (old(c.right) == this && c.right == null)
    ensures this.Acyclic({this})
  {
    var p := this.parent;
    this.parent := null;
    if (p != null) {
      if (p.left == this) {
        p.left := null;
      } else {
        p.right := null;
      }
      var delta := -this.sum;
      p.Adjust(delta, S - {this}, S);
    }
  }

  /*private*/ method Adjust(delta: int, ghost U: set<Composite>, ghost S: set<Composite>)
    requires U <= S && this.Acyclic(U)
    // everything else is valid:
    requires forall c :: c in S && c != this ==> c.Valid(S)
    // this is almost valid:
    requires this.parent != null ==> this.parent in S && (this.parent.left == this || this.parent.right == this)
    requires this.left != null ==> this.left in S && this.left.parent == this && this.left != this.right
    requires this.right != null ==> this.right in S && this.right.parent == this && this.left != this.right
    // ... except that sum needs to be adjusted by delta:
    requires this.sum + delta == this.val + (if this.left == null then 0 else this.left.sum) + (if this.right == null then 0 else this.right.sum)
    // modifies sum fields in U:
    modifies U`sum
    // everything is valid, including this:
    ensures forall c :: c in S ==> c.Valid(S)
  {
    var p: Composite? := this;
    ghost var T := U;
    while (p != null)
      invariant T <= U
      invariant p == null || p.Acyclic(T)
      invariant forall c :: c in S && c != p ==> c.Valid(S)
      invariant p != null ==> p.sum + delta == p.val + (if p.left == null then 0 else p.left.sum) + (if p.right == null then 0 else p.right.sum)
      invariant forall c :: c in S ==> c.left == old(c.left) && c.right == old(c.right) && c.parent == old(c.parent) && c.val == old(c.val)
      decreases T
    {
      p.sum := p.sum + delta;
      T := T - {p};
      p := p.parent;
    }
  }
}

method Main()
{
  var c0 := new Composite;
  c0.Init(57);

  var c1 := new Composite;
  c1.Init(12);
  c0.Add({c0}, c1, {c1});

  var c2 := new Composite;
  c2.Init(48);

  var c3 := new Composite;
  c3.Init(48);
  c2.Add({c2}, c3, {c3});
  c0.Add({c0,c1}, c2, {c2,c3});

  ghost var S := {c0, c1, c2, c3};
  c1.Update(100, S);
  c2.Update(102, S);

  c2.Dislodge(S);
  c2.Update(496, S);
  c0.Update(0, S);
}

method Harness() {
  var a := new Composite;
  a.Init(5);
  var b := new Composite;
  b.Init(7);
  a.Add({a}, b, {b});
  assert a.sum == 12;

  b.Update(17, {a,b});
  assert a.sum == 22;

  var c := new Composite;
  c.Init(10);
  b.Add({a,b}, c, {c});
  b.Dislodge({a,b,c});
  assert b.sum == 27;
}
