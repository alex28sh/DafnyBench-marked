// Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_aula5.dfy

class Set {
  var store: array<int>
  var nelems: int
  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr &&
    this.store in this.Repr &&
    0 < this.store.Length &&
    0 <= this.nelems <= this.store.Length &&
    (forall i :: 
      0 <= i < this.nelems ==>
        this.store[i] in this.elems) &&
    forall x :: 
      x in this.elems ==>
        exists i :: 
          0 <= i < this.nelems &&
          this.store[i] == x
  }
  // pure-end

  constructor (n: int)
    // pre-conditions-start
    requires 0 < n
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures fresh(this.Repr - {this})
    // post-conditions-end
  {
  // impl-start
    this.store := new int[n];
    this.Repr := {this, this.store};
    this.elems := {};
    this.nelems := 0;
  // impl-end
  }

  function size(): int
    requires this.RepInv()
    reads this.Repr
    ensures this.RepInv()
  {
    this.nelems
  }
  // pure-end

  function maxSize(): int
    requires this.RepInv()
    reads this.Repr
    ensures this.RepInv()
  {
    this.store.Length
  }
  // pure-end

  method contains(v: int) returns (b: bool)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures b <==> v in this.elems
    // post-conditions-end
  {
  // impl-start
    var i := this.find(v);
    return i >= 0;
  // impl-end
  }

  method add(v: int)
    // pre-conditions-start
    requires this.RepInv()
    requires this.size() < this.maxSize()
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.Repr
    ensures this.RepInv()
    ensures fresh(this.Repr - old(this.Repr))
    // post-conditions-end
  {
  // impl-start
    var f: int := this.find(v);
    if f < 0 {
      this.store[this.nelems] := v;
      this.elems := this.elems + {v};
      // assert-start
      assert forall i :: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
      // assert-end

      this.nelems := this.nelems + 1;
    }
  // impl-end
  }

  method find(x: int) returns (r: int)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures r < 0 ==> x !in this.elems
    ensures r >= 0 ==> x in this.elems
    // post-conditions-end
  {
  // impl-start
    var i: int := 0;
    while i < this.nelems
      // invariants-start

      invariant 0 <= i <= this.nelems
      invariant forall j :: 0 <= j < i ==> x != this.store[j]
      decreases this.nelems - i
      // invariants-end

    {
      if this.store[i] == x {
        return i;
      }
      i := i + 1;
    }
    return -1;
  // impl-end
  }

  method Main()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var s := new Set(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  // impl-end
  }
}

class PositiveSet {
  var store: array<int>
  var nelems: int
  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr &&
    this.store in this.Repr &&
    0 < this.store.Length &&
    0 <= this.nelems <= this.store.Length &&
    (forall i :: 
      0 <= i < this.nelems ==>
        this.store[i] in this.elems) &&
    (forall x :: 
      x in this.elems ==>
        exists i :: 
          0 <= i < this.nelems &&
          this.store[i] == x) &&
    forall x :: 
      x in this.elems ==>
        x > 0
  }
  // pure-end

  constructor (n: int)
    // pre-conditions-start
    requires 0 < n
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures fresh(this.Repr - {this})
    // post-conditions-end
  {
  // impl-start
    this.store := new int[n];
    this.Repr := {this, this.store};
    this.elems := {};
    this.nelems := 0;
  // impl-end
  }

  function size(): int
    requires this.RepInv()
    reads this.Repr
    ensures this.RepInv()
  {
    this.nelems
  }
  // pure-end

  function maxSize(): int
    requires this.RepInv()
    reads this.Repr
    ensures this.RepInv()
  {
    this.store.Length
  }
  // pure-end

  method contains(v: int) returns (b: bool)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures b <==> v in this.elems
    // post-conditions-end
  {
  // impl-start
    var i := this.find(v);
    return i >= 0;
  // impl-end
  }

  method add(v: int)
    // pre-conditions-start
    requires this.RepInv()
    requires this.size() < this.maxSize()
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.Repr
    ensures this.RepInv()
    ensures fresh(this.Repr - old(this.Repr))
    // post-conditions-end
  {
  // impl-start
    if v > 0 {
      var f: int := this.find(v);
      if f < 0 {
        this.store[this.nelems] := v;
        this.elems := this.elems + {v};
        // assert-start
        assert forall i :: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
        // assert-end

        this.nelems := this.nelems + 1;
      }
    }
  // impl-end
  }

  method find(x: int) returns (r: int)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures r < 0 ==> x !in this.elems
    ensures r >= 0 ==> x in this.elems
    // post-conditions-end
  {
  // impl-start
    var i: int := 0;
    while i < this.nelems
      // invariants-start

      invariant 0 <= i <= this.nelems
      invariant forall j :: 0 <= j < i ==> x != this.store[j]
      decreases this.nelems - i
      // invariants-end

    {
      if this.store[i] == x {
        return i;
      }
      i := i + 1;
    }
    return -1;
  // impl-end
  }

  method Main()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var s := new PositiveSet(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  // impl-end
  }
}

class SavingsAccount {
  var cbalance: int
  var sbalance: int
  ghost var Repr: set<object>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr &&
    this.cbalance >= -this.sbalance / 2
  }
  // pure-end

  ghost predicate PositiveChecking()
    reads this, this.Repr
  {
    this.cbalance >= 0
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures fresh(this.Repr - {this})
    ensures this.RepInv()
    // post-conditions-end
  {
  // impl-start
    this.Repr := {this};
    this.cbalance := 0;
    this.sbalance := 0;
  // impl-end
  }

  method deposit(amount: int)
    // pre-conditions-start
    requires amount > 0
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.RepInv()
    // post-conditions-end
  {
  // impl-start
    this.cbalance := this.cbalance + amount;
  // impl-end
  }

  method withdraw(amount: int)
    // pre-conditions-start
    requires amount > 0
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.RepInv()
    // post-conditions-end
  {
  // impl-start
    if this.cbalance - amount >= -this.sbalance / 2 {
      this.cbalance := this.cbalance - amount;
    }
  // impl-end
  }

  method save(amount: int)
    // pre-conditions-start
    requires amount > 0
    requires this.PositiveChecking()
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.RepInv()
    // post-conditions-end
  {
  // impl-start
    if this.cbalance >= 0 {
      this.sbalance := this.sbalance + amount;
    }
  // impl-end
  }

  method rescue(amount: int)
    // pre-conditions-start
    requires amount > 0
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.RepInv()
    // post-conditions-end
  {
  // impl-start
    if this.cbalance >= -(this.sbalance - amount) / 2 {
      this.sbalance := this.sbalance - amount;
    }
  // impl-end
  }
}

class GrowingSet {
  var store: array<int>
  var nelems: int
  ghost var Repr: set<object>
  ghost var elems: set<int>

  ghost predicate RepInv()
    reads this, this.Repr
  {
    this in this.Repr &&
    this.store in this.Repr &&
    0 < this.store.Length &&
    0 <= this.nelems <= this.store.Length &&
    (forall i :: 
      0 <= i < this.nelems ==>
        this.store[i] in this.elems) &&
    forall x :: 
      x in this.elems ==>
        exists i :: 
          0 <= i < this.nelems &&
          this.store[i] == x
  }
  // pure-end

  constructor (n: int)
    // pre-conditions-start
    requires 0 < n
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures fresh(this.Repr - {this})
    // post-conditions-end
  {
  // impl-start
    this.store := new int[n];
    this.Repr := {this, this.store};
    this.elems := {};
    this.nelems := 0;
  // impl-end
  }

  function size(): int
    requires this.RepInv()
    reads this.Repr
    ensures this.RepInv()
  {
    this.nelems
  }
  // pure-end

  function maxSize(): int
    requires this.RepInv()
    reads this.Repr
    ensures this.RepInv()
  {
    this.store.Length
  }
  // pure-end

  method contains(v: int) returns (b: bool)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures b <==> v in this.elems
    // post-conditions-end
  {
  // impl-start
    var i := this.find(v);
    return i >= 0;
  // impl-end
  }

  method add(v: int)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.RepInv()
    ensures fresh(this.Repr - old(this.Repr))
    // post-conditions-end
  {
  // impl-start
    var f: int := this.find(v);
    // assert-start
    assert forall i :: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
    // assert-end

    if f < 0 {
      if this.nelems == this.store.Length {
        var tmp := new int[this.store.Length * 2];
        var i := 0;
        while i < this.store.Length
          // invariants-start

          invariant 0 <= i <= this.store.Length < tmp.Length
          invariant forall j :: 0 <= j < i ==> old(this.store[j]) == tmp[j]
          modifies tmp
          // invariants-end

        {
          tmp[i] := this.store[i];
          i := i + 1;
        }
        this.Repr := this.Repr - {this.store} + {tmp};
        this.store := tmp;
      }
      this.store[this.nelems] := v;
      this.elems := this.elems + {v};
      // assert-start
      assert forall i :: 0 <= i < this.nelems ==> old(this.store[i]) == this.store[i];
      // assert-end

      this.nelems := this.nelems + 1;
    }
  // impl-end
  }

  method find(x: int) returns (r: int)
    // pre-conditions-start
    requires this.RepInv()
    // pre-conditions-end
    // post-conditions-start
    ensures this.RepInv()
    ensures r < 0 ==> x !in this.elems
    ensures r >= 0 ==> x in this.elems
    // post-conditions-end
  {
  // impl-start
    var i: int := 0;
    while i < this.nelems
      // invariants-start

      invariant 0 <= i <= this.nelems
      invariant forall j :: 0 <= j < i ==> x != this.store[j]
      decreases this.nelems - i
      // invariants-end

    {
      if this.store[i] == x {
        return i;
      }
      i := i + 1;
    }
    return -1;
  // impl-end
  }

  method Main()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var s := new GrowingSet(10);
    if s.size() < s.maxSize() {
      s.add(2);
      var b := s.contains(2);
      if s.size() < s.maxSize() {
        s.add(3);
      }
    }
  // impl-end
  }
}
