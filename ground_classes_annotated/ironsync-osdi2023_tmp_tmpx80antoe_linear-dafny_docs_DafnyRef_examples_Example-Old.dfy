// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old.dfy

class A {
  var value: int

  method m(i: int)
    // pre-conditions-start
    requires i == 6
    requires this.value == 42
    // pre-conditions-end
    // post-conditions-start
    modifies this
    // post-conditions-end
  {
  // impl-start
    var j: int := 17;
    this.value := 43;
    label L:
    j := 18;
    this.value := 44;
    label M:
    // assert-start
    assert old(i) == 6;
    // assert-end

    // assert-start
    assert old(j) == 18;
    // assert-end

    // assert-start
    assert old@L(j) == 18;
    // assert-end

    // assert-start
    assert old(this.value) == 42;
    // assert-end

    // assert-start
    assert old@L(this.value) == 43;
    // assert-end

    // assert-start
    assert old@M(this.value) == 44 && this.value == 44;
    // assert-end

  // impl-end
  }
}
