// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_Bug92.dfy


module ModOpaque {
  function {:opaque} Hidden(x: int): (int, int)
  {
    (5, 7)
  }
  // pure-end

  function Visible(x: int): (int, int)
  {
    Hidden(x)
  }
  // pure-end

  lemma foo(x: int, y: int, z: int)
    // pre-conditions-start
    requires (y, z) == Visible(x)
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Hidden(x);
  // impl-end
  }

  lemma bar(x: int, y: int, z: int)
    // pre-conditions-start
    requires y == Visible(x).0
    requires z == Visible(x).1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Visible(x);
  // impl-end
  }

  lemma baz(x: int, y: int, z: int)
    // pre-conditions-start
    requires y == Visible(x).0
    requires z == Visible(x).1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Hidden(x);
  // impl-end
  }
}

module ModVisible {
  function Hidden(x: int): (int, int)
  {
    (5, 7)
  }
  // pure-end

  function Visible(x: int): (int, int)
  {
    Hidden(x)
  }
  // pure-end

  lemma foo(x: int, y: int, z: int)
    // pre-conditions-start
    requires (y, z) == Visible(x)
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Hidden(x);
  // impl-end
  }

  lemma bar(x: int, y: int, z: int)
    // pre-conditions-start
    requires y == Visible(x).0
    requires z == Visible(x).1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Visible(x);
  // impl-end
  }

  lemma baz(x: int, y: int, z: int)
    // pre-conditions-start
    requires y == Visible(x).0
    requires z == Visible(x).1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Hidden(x);
  // impl-end
  }
}

module ModFuel {
  function {:fuel 0, 0} Hidden(x: int): (int, int)
  {
    (5, 7)
  }
  // pure-end

  function Visible(x: int): (int, int)
  {
    Hidden(x)
  }
  // pure-end

  lemma foo(x: int, y: int, z: int)
    // pre-conditions-start
    requires (y, z) == Visible(x)
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Hidden(x);
  // impl-end
  }

  lemma bar(x: int, y: int, z: int)
    // pre-conditions-start
    requires y == Visible(x).0
    requires z == Visible(x).1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Visible(x);
  // impl-end
  }

  lemma baz(x: int, y: int, z: int)
    // pre-conditions-start
    requires y == Visible(x).0
    requires z == Visible(x).1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    assert (y, z) == Hidden(x);
  // impl-end
  }
}
