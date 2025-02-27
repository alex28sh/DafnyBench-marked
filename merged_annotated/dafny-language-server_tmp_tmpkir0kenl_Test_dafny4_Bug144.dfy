// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug144.dfy

predicate p(i: int)
// pure-end

method m1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end

method m2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assume exists i :: p(i);
  // assert-end

  // assert-start
  assert exists i :: p(i);
  // assert-end

  m1();
  // assert-start
  assert exists i :: p(i);
  // assert-end

// impl-end
}

class Test {
  var arr: array<int>

  predicate p(i: int)
  // pure-end

  method foo()
    // pre-conditions-start
    requires this.arr.Length > 0
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr
    // post-conditions-end
  {
  // impl-start
    // assert-start
    assume exists i :: this.p(i);
    // assert-end

    this.arr[0] := 1;
    // assert-start
    assert exists i :: this.p(i);
    // assert-end

  // impl-end
  }
}
