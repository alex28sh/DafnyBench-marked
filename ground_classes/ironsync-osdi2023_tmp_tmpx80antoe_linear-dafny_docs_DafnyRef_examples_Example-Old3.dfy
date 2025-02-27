class A {
  var z1: array<nat>
  var z2: array<nat>

  method mm()
    requires this.z1.Length > 10 && this.z1[0] == 7
    requires this.z2.Length > 10 && this.z2[0] == 17
    modifies this.z2
  {
    var a: array<nat> := this.z1;
    assert a[0] == 7;
    a := this.z2;
    assert a[0] == 17;
    assert old(a[0]) == 17; // a is local with value z2
    this.z2[0] := 27;
    assert old(a[0]) == 17; // a is local, with current value of
                            // z2; in pre-state z2[0] == 17
    assert old(a)[0] == 27; // a is local, with current value of
                            // z2; z2[0] is currently 27
  }
}
