// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week10_BoundedQueue_01.dfy

class BoundedQueue<T(0)> {
  ghost var contents: seq<T>
  ghost var N: nat
  ghost var Repr: set<object>
  var data: array<T>
  var wr: nat
  var rd: nat

  ghost predicate Valid()
    reads this, this.Repr
    ensures this.Valid() ==> this in this.Repr && |this.contents| <= this.N
  {
    this in this.Repr &&
    this.data in this.Repr &&
    this.data.Length == this.N + 1 &&
    this.wr <= this.N &&
    this.rd <= this.N &&
    this.contents == if this.rd <= this.wr then this.data[this.rd .. this.wr] else this.data[this.rd..] + this.data[..this.wr]
  }
  // pure-end

  constructor (N: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.Valid() && fresh(this.Repr)
    ensures this.contents == [] && this.N == N
    // post-conditions-end
  {
  // impl-start
    this.contents := [];
    this.N := N;
    this.data := new T[N + 1];
    this.rd, this.wr := 0, 0;
    this.Repr := {this, this.data};
  // impl-end
  }

  method Insert(x: T)
    // pre-conditions-start
    requires this.Valid()
    requires |this.contents| != this.N
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.contents == old(this.contents) + [x]
    ensures this.N == old(this.N)
    ensures this.Valid() && fresh(this.Repr - old(this.Repr))
    // post-conditions-end
  {
  // impl-start
    this.contents := old(this.contents) + [x];
    this.data[this.wr] := x;
    // assert-start
    assert (this.wr == this.data.Length - 1 ==> this.contents == if this.rd <= 0 then this.data[this.rd .. 0] else this.data[this.rd..] + this.data[..0]) && (this.wr != this.data.Length - 1 ==> this.contents == if this.rd <= this.wr + 1 then this.data[this.rd .. this.wr + 1] else this.data[this.rd..] + this.data[..this.wr + 1]);
    // assert-end

    if this.wr == this.data.Length - 1 {
      // assert-start
      assert this.contents == if this.rd <= 0 then this.data[this.rd .. 0] else this.data[this.rd..] + this.data[..0];
      // assert-end

      this.wr := 0;
      // assert-start
      assert this.contents == if this.rd <= this.wr then this.data[this.rd .. this.wr] else this.data[this.rd..] + this.data[..this.wr];
      // assert-end

    } else {
      // assert-start
      assert this.contents == if this.rd <= this.wr + 1 then this.data[this.rd .. this.wr + 1] else this.data[this.rd..] + this.data[..this.wr + 1];
      // assert-end

      this.wr := this.wr + 1;
      // assert-start
      assert this.contents == if this.rd <= this.wr then this.data[this.rd .. this.wr] else this.data[this.rd..] + this.data[..this.wr];
      // assert-end

    }
    // assert-start
    assert this.contents == if this.rd <= this.wr then this.data[this.rd .. this.wr] else this.data[this.rd..] + this.data[..this.wr];
    // assert-end

  // impl-end
  }

  method Remove() returns (x: T)
    // pre-conditions-start
    requires this.Valid()
    requires |this.contents| != 0
    // pre-conditions-end
    // post-conditions-start
    modifies this.Repr
    ensures this.contents == old(this.contents[1..]) && old(this.contents[0]) == x
    ensures this.N == old(this.N)
    ensures this.Valid() && fresh(this.Repr - old(this.Repr))
    // post-conditions-end
  {
  // impl-start
    this.contents := this.contents[1..];
    x := this.data[this.rd];
    if this.rd == this.data.Length - 1 {
      this.rd := 0;
    } else {
      this.rd := this.rd + 1;
    }
  // impl-end
  }
}
