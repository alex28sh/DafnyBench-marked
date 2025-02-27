// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_ExtensibleArray.dfy

class ExtensibleArray<T(0)> {
  ghost var Elements: seq<T>
  ghost var Repr: set<object>
  var front: array?<T>
  var depot: ExtensibleArray?<array<T>>
  var length: int
  var M: int

  ghost predicate Valid()
    reads this, this.Repr
    ensures this.Valid() ==> this in this.Repr
    decreases this.Repr + {this}
  {
    this in this.Repr &&
    (this.front != null ==>
      this.front in this.Repr) &&
    (this.depot != null ==>
      this.depot in this.Repr &&
      this.depot.Repr <= this.Repr &&
      forall j :: 
        0 <= j < |this.depot.Elements| ==>
          this.depot.Elements[j] in this.Repr) &&
    (this.depot != null ==>
      this !in this.depot.Repr &&
      this.front !in this.depot.Repr &&
      forall j :: 
        0 <= j < |this.depot.Elements| ==>
          this.depot.Elements[j] !in this.depot.Repr &&
          this.depot.Elements[j] != this.front &&
          forall k :: 
            0 <= k < |this.depot.Elements| &&
            k != j ==>
              this.depot.Elements[j] != this.depot.Elements[k]) &&
    (this.front != null ==>
      this.front.Length == 256) &&
    (this.depot != null ==>
      this.depot.Valid() &&
      forall j :: 
        0 <= j < |this.depot.Elements| ==>
          this.depot.Elements[j].Length == 256) &&
    (this.length == this.M <==> this.front == null) &&
    this.M == (if this.depot == null then 0 else 256 * |this.depot.Elements|) &&
    this.length == |this.Elements| &&
    this.M <= |this.Elements| < this.M + 256 &&
    (forall i :: 
      0 <= i < this.M ==>
        this.Elements[i] == this.depot.Elements[i / 256][i % 256]) &&
    forall i :: 
      this.M <= i < this.length ==>
        this.Elements[i] == this.front[i - this.M]
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.Valid() && fresh(this.Repr) && this.Elements == []
    // post-conditions-end
  {
  // impl-start
    this.front, this.depot := null, null;
    this.length, this.M := 0, 0;
    this.Elements, this.Repr := [], {this};
  // impl-end
  }

  function Get(i: int): T
    requires this.Valid() && 0 <= i < |this.Elements|
    reads this.Repr
    ensures this.Get(i) == this.Elements[i]
  {
    if this.M <= i then
      this.front[i - this.M]
    else
      this.depot.Get(i / 256)[i % 256]
  }
  // pure-end

  method Set(i: int, t: T)
    // pre-conditions-start
    requires this.Valid() && 0 <= i < |this.Elements|
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.Valid() && fresh(this.Repr - old(this.Repr))
    ensures this.Elements == old(this.Elements)[i := t]
    // post-conditions-end
  {
  // impl-start
    if this.M <= i {
      this.front[i - this.M] := t;
    } else {
      this.depot.Get(i / 256)[i % 256] := t;
    }
    this.Elements := this.Elements[i := t];
  // impl-end
  }

  method Add(t: T)
    // pre-conditions-start
    requires this.Valid()
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.Valid() && fresh(this.Repr - old(this.Repr))
    ensures this.Elements == old(this.Elements) + [t]
    decreases |this.Elements|
    // post-conditions-end
  {
  // impl-start
    if this.front == null {
      this.front := new T[256];
      this.Repr := this.Repr + {this.front};
    }
    this.front[this.length - this.M] := t;
    this.length := this.length + 1;
    this.Elements := this.Elements + [t];
    if this.length == this.M + 256 {
      if this.depot == null {
        this.depot := new ExtensibleArray();
      }
      this.depot.Add(this.front);
      this.Repr := this.Repr + this.depot.Repr;
      this.M := this.M + 256;
      this.front := null;
    }
  // impl-end
  }
}
