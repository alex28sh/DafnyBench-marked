// Formal_Verification_With_Dafny_tmp_tmp5j79rq48_Counter.dfy

class Counter {
  var value: int

  constructor init()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.value == 0
    // post-conditions-end
  {
  // impl-start
    this.value := 0;
  // impl-end
  }

  method getValue() returns (x: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures x == this.value
    // post-conditions-end
  {
  // impl-start
    x := this.value;
  // impl-end
  }

  method inc()
    // pre-conditions-start
    requires this.value >= 0
    // pre-conditions-end
    // post-conditions-start
    modifies `value
    ensures this.value == old(this.value) + 1
    // post-conditions-end
  {
  // impl-start
    this.value := this.value + 1;
  // impl-end
  }

  method dec()
    // pre-conditions-start
    requires this.value > 0
    // pre-conditions-end
    // post-conditions-start
    modifies `value
    ensures this.value == old(this.value) - 1
    // post-conditions-end
  {
  // impl-start
    this.value := this.value - 1;
  // impl-end
  }

  method Main()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var count := new Counter.init();
    count.inc();
    count.inc();
    count.dec();
    count.inc();
    var aux: int := count.getValue();
    // assert-start
    assert aux == 2;
    // assert-end

  // impl-end
  }
}
