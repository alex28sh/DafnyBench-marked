class A {

  var value: int

  method m(i: int)
    requires i == 6
    requires this.value == 42
    modifies this
  {
    var j: int := 17;
    this.value := 43;
    label L:
    j := 18;
    this.value := 44;
    label M:
    assert old(i) == 6; // i is local, but can't be changed anyway
    assert old(j) == 18; // j is local and not affected by old
    assert old@L(j) == 18; // j is local and not affected by old
    assert old(this.value) == 42;
    assert old@L(this.value) == 43;
    assert old@M(this.value) == 44 && this.value == 44;
    // value is this.value; 'this' is the same
    // same reference in current and pre state but the
    // values stored in the heap as its fields are different;
    // '.value' evaluates to 42 in the pre-state, 43 at L,
    // and 44 in the current state
  }
}
