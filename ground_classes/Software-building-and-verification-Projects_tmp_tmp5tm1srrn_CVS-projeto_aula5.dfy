class Set {
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr && this.store in this.Repr &&
    0 < this.store.Length
    && 0 <= this.nelems <= this.store.Length
    && (forall i :: 0 <= i < this.nelems ==> this.store[i] in this.elems)
    && (forall x :: x in this.elems ==> exists i :: 0 <= i < this.nelems && this.store[i] == x)
  }

  constructor(n: int)
    requires 0 < n
    ensures this.RepInv()
    ensures fresh(this.Repr - {this})
  {
    this.store := new int[n];
    this.Repr := {this, this.store};
    this.elems := {};
    this.nelems := 0;
  }

  function size(): int
    requires this.RepInv()
    ensures this.RepInv()
    reads this.Repr
  { this.nelems }

  function maxSize(): int
    requires this.RepInv()
    ensures this.RepInv()
    reads this.Repr
  { this.store.Length }

  method contains(v: int) returns (b: bool)
    requires this.RepInv()
    ensures this.RepInv()
    ensures b <==> v in this.elems
  {
    var i := this.find(v);
    return i >= 0;
  }

  method add(v: int)
    requires this.RepInv()
    requires this.size() < this.maxSize()
    ensures this.RepInv()
    modifies this, this.Repr
    ensures fresh(this.Repr - old(this.Repr))
  {
    var f: int := this.find(v);
    if (f < 0) {
      this.store[this.nelems] := v;
      this.elems := this.elems + {v};
      assert forall i:: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
      this.nelems := this.nelems + 1;
    }
  }

  method find(x: int) returns (r: int)
    requires this.RepInv()
    ensures this.RepInv()
    ensures r < 0 ==> x !in this.elems
    ensures r >= 0 ==> x in this.elems
  {
    var i: int := 0;
    while (i < this.nelems)
      decreases this.nelems - i
      invariant 0 <= i <= this.nelems
      invariant forall j::(0 <= j < i) ==> x != this.store[j]
    {
      if (this.store[i] == x) { return i; }
      i := i + 1;
    }
    return -1;
  }

  method Main()
  {
    var s := new Set(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

class PositiveSet {
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr && this.store in this.Repr &&
    0 < this.store.Length
    && 0 <= this.nelems <= this.store.Length
    && (forall i :: 0 <= i < this.nelems ==> this.store[i] in this.elems)
    && (forall x :: x in this.elems ==> exists i :: 0 <= i < this.nelems && this.store[i] == x)
    && (forall x :: x in this.elems ==> x > 0)
  }

  constructor(n: int)
    requires 0 < n
    ensures this.RepInv()
    ensures fresh(this.Repr - {this})
  {
    this.store := new int[n];
    this.Repr := {this, this.store};
    this.elems := {};
    this.nelems := 0;
  }

  function size(): int
    requires this.RepInv()
    ensures this.RepInv()
    reads this.Repr
  { this.nelems }

  function maxSize(): int
    requires this.RepInv()
    ensures this.RepInv()
    reads this.Repr
  { this.store.Length }

  method contains(v: int) returns (b: bool)
    requires this.RepInv()
    ensures this.RepInv()
    ensures b <==> v in this.elems
  {
    var i := this.find(v);
    return i >= 0;
  }

  method add(v: int)
    requires this.RepInv()
    requires this.size() < this.maxSize()
    ensures this.RepInv()
    modifies this, this.Repr
    ensures fresh(this.Repr - old(this.Repr))
  {
    if (v > 0) {
      var f: int := this.find(v);
      if (f < 0) {
        this.store[this.nelems] := v;
        this.elems := this.elems + {v};
        assert forall i:: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
        this.nelems := this.nelems + 1;
      }
    }
  }

  method find(x: int) returns (r: int)
    requires this.RepInv()
    ensures this.RepInv()
    ensures r < 0 ==> x !in this.elems
    ensures r >= 0 ==> x in this.elems
  {
    var i: int := 0;
    while (i < this.nelems)
      decreases this.nelems - i
      invariant 0 <= i <= this.nelems
      invariant forall j::(0 <= j < i) ==> x != this.store[j]
    {
      if (this.store[i] == x) { return i; }
      i := i + 1;
    }
    return -1;
  }

  method Main()
  {
    var s := new PositiveSet(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}

class SavingsAccount {
  var cbalance: int;
  var sbalance: int;

  ghost var Repr: set<object>;

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr
    && this.cbalance >= -this.sbalance / 2
  }

  ghost predicate PositiveChecking()
    reads this, this.Repr
  {
    this.cbalance >= 0
  }

  constructor()
    ensures fresh(this.Repr - {this})
    ensures this.RepInv()
  {
    this.Repr := {this};
    this.cbalance := 0;
    this.sbalance := 0;
  }

  method deposit(amount: int)
    requires amount > 0
    requires this.RepInv()
    ensures this.RepInv()
    modifies this.Repr
  {
    this.cbalance := this.cbalance + amount;
  }

  method withdraw(amount: int)
    requires amount > 0
    requires this.RepInv()
    ensures this.RepInv()
    modifies this.Repr
  {
    if (this.cbalance - amount >= -this.sbalance / 2) {
      this.cbalance := this.cbalance - amount;
    }
  }

  method save(amount: int)
    requires amount > 0
    requires this.PositiveChecking()
    requires this.RepInv()
    ensures this.RepInv()
    modifies this.Repr
  {
    if (this.cbalance >= 0) {
      this.sbalance := this.sbalance + amount;
    }
  }

  method rescue(amount: int)
    requires amount > 0
    requires this.RepInv()
    ensures this.RepInv()
    modifies this.Repr
  {
    if (this.cbalance >= -(this.sbalance - amount) / 2) {
      this.sbalance := this.sbalance - amount;
    }
  }
}

class GrowingSet {
  var store: array<int>;
  var nelems: int;

  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr && this.store in this.Repr &&
    0 < this.store.Length
    && 0 <= this.nelems <= this.store.Length
    && (forall i :: 0 <= i < this.nelems ==> this.store[i] in this.elems)
    && (forall x :: x in this.elems ==> exists i :: 0 <= i < this.nelems && this.store[i] == x)
  }

  constructor(n: int)
    requires 0 < n
    ensures this.RepInv()
    ensures fresh(this.Repr - {this})
  {
    this.store := new int[n];
    this.Repr := {this, this.store};
    this.elems := {};
    this.nelems := 0;
  }

  function size(): int
    requires this.RepInv()
    ensures this.RepInv()
    reads this.Repr
  { this.nelems }

  function maxSize(): int
    requires this.RepInv()
    ensures this.RepInv()
    reads this.Repr
  { this.store.Length }

  method contains(v: int) returns (b: bool)
    requires this.RepInv()
    ensures this.RepInv()
    ensures b <==> v in this.elems
  {
    var i := this.find(v);
    return i >= 0;
  }

  method add(v: int)
    requires this.RepInv()
    ensures this.RepInv()
    modifies this.Repr
    ensures fresh(this.Repr - old(this.Repr))
  {
    var f: int := this.find(v);
    assert forall i:: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
    if (f < 0) {
      if (this.nelems == this.store.Length) {
        var tmp := new int[this.store.Length * 2];
        var i := 0;
        while i < this.store.Length
          invariant 0 <= i <= this.store.Length < tmp.Length
          invariant forall j :: 0 <= j < i ==> old(this.store[j]) == tmp[j]
          modifies tmp
        {
          tmp[i] := this.store[i];
          i := i + 1;
        }
        this.Repr := this.Repr - {this.store} + {tmp};
        this.store := tmp;
      }

      this.store[this.nelems] := v;
      this.elems := this.elems + {v};
      assert forall i:: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
      this.nelems := this.nelems + 1;
    }
  }

  method find(x: int) returns (r: int)
    requires this.RepInv()
    ensures this.RepInv()
    ensures r < 0 ==> x !in this.elems
    ensures r >= 0 ==> x in this.elems
  {
    var i: int := 0;
    while (i < this.nelems)
      decreases this.nelems - i
      invariant 0 <= i <= this.nelems
      invariant forall j::(0 <= j < i) ==> x != this.store[j]
    {
      if (this.store[i] == x) { return i; }
      i := i + 1;
    }
    return -1;
  }

  method Main()
  {
    var s := new GrowingSet(10);
    if (s.size() < s.maxSize()) {
      s.add(2);
      var b := s.contains(2);
      if (s.size() < s.maxSize()) {
        s.add(3);
      }
    }
  }
}
