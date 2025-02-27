// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old2.dfy

class A {
  var value: int

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.value == 10
    // post-conditions-end
  {
  // impl-start
    this.value := 10;
  // impl-end
  }
}

class B {
  var a: A

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    this.a := new A();
  // impl-end
  }

  method m()
    // pre-conditions-start
    requires this.a.value == 11
    // pre-conditions-end
    // post-conditions-start
    modifies this, this.a
    // post-conditions-end
  {
  // impl-start
    label L:
    this.a.value := 12;
    label M:
    this.a := new A();
    label N:
    this.a.value := 20;
    label P:
    // assert-start
    assert old(this.a.value) == 11;
    // assert-end

    // assert-start
    assert old(this.a).value == 12;
    // assert-end

    // assert-start
    assert old@L(this.a.value) == 11;
    // assert-end

    // assert-start
    assert old@L(this.a).value == 12;
    // assert-end

    // assert-start
    assert old@M(this.a.value) == 12;
    // assert-end

    // assert-start
    assert old@M(this.a).value == 12;
    // assert-end

    // assert-start
    assert old@N(this.a.value) == 10;
    // assert-end

    // assert-start
    assert old@N(this.a).value == 20;
    // assert-end

    // assert-start
    assert old@P(this.a.value) == 20;
    // assert-end

    // assert-start
    assert old@P(this.a).value == 20;
    // assert-end

  // impl-end
  }
}
