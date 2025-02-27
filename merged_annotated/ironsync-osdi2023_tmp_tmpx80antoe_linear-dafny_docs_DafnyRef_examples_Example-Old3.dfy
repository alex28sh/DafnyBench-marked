// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_docs_DafnyRef_examples_Example-Old3.dfy

class A {
  var z1: array<nat>
  var z2: array<nat>

  method mm()
    // pre-conditions-start
    requires this.z1.Length > 10 && this.z1[0] == 7
    requires this.z2.Length > 10 && this.z2[0] == 17
    // pre-conditions-end
    // post-conditions-start
    modifies this.z2
    // post-conditions-end
  {
  // impl-start
    var a: array<nat> := this.z1;
    // assert-start
    assert a[0] == 7;
    // assert-end

    a := this.z2;
    // assert-start
    assert a[0] == 17;
    // assert-end

    // assert-start
    assert old(a[0]) == 17;
    // assert-end

    this.z2[0] := 27;
    // assert-start
    assert old(a[0]) == 17;
    // assert-end

    // assert-start
    assert old(a)[0] == 27;
    // assert-end

  // impl-end
  }
}
