method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  test0(10);
  test5(11);
  test6(12);
  test1();
  test2();
// impl-end
}

function valid(x: int): bool
{
  x > 0
}
// pure-end

function ref1(y: int): int
  requires valid(y)
{
  y - 1
}
// pure-end

lemma assumption1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b
  // post-conditions-end
{
// impl-start
// impl-end
}

method test0(a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if ref1.requires(a) {
    ghost var b := ref1(a);
  }
// impl-end
}

method test5(a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if valid(a) {
    // assert-start
    assert ref1.requires(a);
    // assert-end

  }
// impl-end
}

method test6(a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if ref1.requires(a) {
    // assert-start
    assert valid(a);
    // assert-end

  }
// impl-end
}

method test1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if * {
    // assert-start
    assert forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
    // assert-end

  } else {
    // assert-start
    assert forall a, b :: ref1.requires(a) && ref1.requires(b) && ref1(a) == ref1(b) ==> a == b;
    // assert-end

  }
// impl-end
}

function {:opaque} ref2(y: int): int
  requires valid(y)
{
  y - 1
}
// pure-end

lemma assumption2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b
  // post-conditions-end
{
// impl-start
  reveal ref2();
// impl-end
}

method test2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assumption2();
  // assert-end

  if * {
    // assert-start
    assert forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
    // assert-end

  } else {
    // assert-start
    assert forall a, b :: ref2.requires(a) && ref2.requires(b) && ref2(a) == ref2(b) ==> a == b;
    // assert-end

  }
// impl-end
}
