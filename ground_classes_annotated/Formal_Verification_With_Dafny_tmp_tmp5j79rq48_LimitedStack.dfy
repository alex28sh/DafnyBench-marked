// Formal_Verification_With_Dafny_tmp_tmp5j79rq48_LimitedStack.dfy

class LimitedStack {
  var capacity: int
  var arr: array<int>
  var top: int

  predicate Valid()
    reads this
  {
    this.arr != null &&
    this.capacity > 0 &&
    this.capacity == this.arr.Length &&
    this.top >= -1 &&
    this.top < this.capacity
  }
  // pure-end

  predicate Empty()
    reads `top
  {
    this.top == -1
  }
  // pure-end

  predicate Full()
    reads `top, `capacity
  {
    this.top == this.capacity - 1
  }
  // pure-end

  method Init(c: int)
    // pre-conditions-start
    requires c > 0
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid() && this.Empty() && c == this.capacity
    ensures fresh(this.arr)
    // post-conditions-end
  {
  // impl-start
    this.capacity := c;
    this.arr := new int[c];
    this.top := -1;
  // impl-end
  }

  method isEmpty() returns (res: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures res == this.Empty()
    // post-conditions-end
  {
  // impl-start
    if this.top == -1 {
      return true;
    } else {
      return false;
    }
  // impl-end
  }

  method Peek() returns (elem: int)
    // pre-conditions-start
    requires this.Valid() && !this.Empty()
    // pre-conditions-end
    // post-conditions-start
    ensures elem == this.arr[this.top]
    // post-conditions-end
  {
  // impl-start
    return this.arr[this.top];
  // impl-end
  }

  method Push(elem: int)
    // pre-conditions-start
    requires this.Valid()
    requires !this.Full()
    // pre-conditions-end
    // post-conditions-start
    modifies `top, this.arr
    ensures this.Valid() && this.top == old(this.top) + 1 && this.arr[this.top] == elem
    ensures !old(this.Empty()) ==> forall i: int :: 0 <= i <= old(this.top) ==> this.arr[i] == old(this.arr[i])
    // post-conditions-end
  {
  // impl-start
    this.top := this.top + 1;
    this.arr[this.top] := elem;
  // impl-end
  }

  method Pop() returns (elem: int)
    // pre-conditions-start
    requires this.Valid() && !this.Empty()
    // pre-conditions-end
    // post-conditions-start
    modifies `top
    ensures this.Valid() && this.top == old(this.top) - 1
    ensures elem == this.arr[old(this.top)]
    // post-conditions-end
  {
  // impl-start
    elem := this.arr[this.top];
    this.top := this.top - 1;
    return elem;
  // impl-end
  }

  method Shift()
    // pre-conditions-start
    requires this.Valid() && !this.Empty()
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr, `top
    ensures this.Valid()
    ensures forall i: int :: 0 <= i < this.capacity - 1 ==> this.arr[i] == old(this.arr[i + 1])
    ensures this.top == old(this.top) - 1
    // post-conditions-end
  {
  // impl-start
    var i: int := 0;
    while i < this.capacity - 1
      // invariants-start

      invariant 0 <= i < this.capacity
      invariant this.top == old(this.top)
      invariant forall j: int :: 0 <= j < i ==> this.arr[j] == old(this.arr[j + 1])
      invariant forall j: int :: i <= j < this.capacity ==> this.arr[j] == old(this.arr[j])
      // invariants-end

    {
      this.arr[i] := this.arr[i + 1];
      i := i + 1;
    }
    this.top := this.top - 1;
  // impl-end
  }

  method Push2(elem: int)
    // pre-conditions-start
    requires this.Valid()
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr, `top
    ensures this.Valid() && !this.Empty()
    ensures this.arr[this.top] == elem
    ensures old(!this.Full()) ==> this.top == old(this.top) + 1 && old(this.Full()) ==> this.top == old(this.top)
    ensures (old(this.Full()) ==> this.arr[this.capacity - 1] == elem) && (old(!this.Full()) ==> this.top == old(this.top) + 1 && this.arr[this.top] == elem)
    ensures old(this.Full()) ==> forall i: int :: 0 <= i < this.capacity - 1 ==> this.arr[i] == old(this.arr[i + 1])
    // post-conditions-end
  {
  // impl-start
    if top == capacity - 1 {
      Shift();
      top := top + 1;
      this.arr[this.top] := elem;
    } else {
      top := top + 1;
      this.arr[this.top] := elem;
    }
  // impl-end
  }

  method Main()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var s := new LimitedStack;
    s.Init(3);
    // assert-start
    assert s.Empty() && !s.Full();
    // assert-end

    s.Push(27);
    // assert-start
    assert !s.Empty();
    // assert-end

    var e := s.Pop();
    // assert-start
    assert e == 27;
    // assert-end

    // assert-start
    assert s.top == -1;
    // assert-end

    // assert-start
    assert s.Empty() && !s.Full();
    // assert-end

    s.Push(5);
    // assert-start
    assert s.top == 0;
    // assert-end

    // assert-start
    assert s.capacity == 3;
    // assert-end

    s.Push(32);
    s.Push(9);
    // assert-start
    assert s.Full();
    // assert-end

    // assert-start
    assert s.arr[0] == 5;
    // assert-end

    var e2 := s.Pop();
    // assert-start
    assert e2 == 9 && !s.Full();
    // assert-end

    // assert-start
    assert s.arr[0] == 5;
    // assert-end

    s.Push(e2);
    s.Push2(99);
    var e3 := s.Peek();
    // assert-start
    assert e3 == 99;
    // assert-end

    // assert-start
    assert s.arr[0] == 32;
    // assert-end

  // impl-end
  }
}
