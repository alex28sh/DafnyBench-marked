

module ProdCons {
  type Process(==)

  type T

  class ProdCons {
    const P: set<Process>
    var maxBufferSize: nat
    var buffer: seq<T>

    predicate valid()
      reads this
    {
      maxBufferSize > 0 &&
      P != {} &&
      0 <= |buffer| <= maxBufferSize
    }
    // pure-end

    constructor (processes: set<Process>, m: nat)
      // pre-conditions-start
      requires processes != {}
      requires m >= 1
      // pre-conditions-end
      // post-conditions-start
      ensures this.valid()
      // post-conditions-end
    {
    // impl-start
      P := processes;
      buffer := [];
      maxBufferSize := m;
    // impl-end
    }

    predicate putEnabled(p: Process)
      reads this
    {
      |buffer| < maxBufferSize
    }
    // pure-end

    method put(p: Process, t: T)
      // pre-conditions-start
      requires this.valid()
      requires this.putEnabled(p)
      // pre-conditions-end
      // post-conditions-start
      modifies this
      // post-conditions-end
    {
    // impl-start
      buffer := buffer + [t];
    // impl-end
    }

    predicate getEnabled(p: Process)
      reads this
    {
      |buffer| >= 1
    }
    // pure-end

    method get(p: Process)
      // pre-conditions-start
      requires this.getEnabled(p)
      requires this.valid()
      // pre-conditions-end
      // post-conditions-start
      modifies this
      ensures |this.buffer| == |old(this.buffer)| - 1
      // post-conditions-end
    {
    // impl-start
      buffer := buffer[1..];
    // impl-end
    }

    lemma noDeadlock()
      // pre-conditions-start
      requires this.valid()
      // pre-conditions-end
      // post-conditions-start
      ensures exists p :: p in P && (this.getEnabled(p) || this.putEnabled(p))
      // post-conditions-end
    {
    // impl-start
      var p: Process :| p in P;
      if |buffer| > 0 {
        assert getEnabled(p);
      } else {
        assert |buffer| == 0;
        assert |buffer| < maxBufferSize;
        assert putEnabled(p);
      }
    // impl-end
    }
  }
}
