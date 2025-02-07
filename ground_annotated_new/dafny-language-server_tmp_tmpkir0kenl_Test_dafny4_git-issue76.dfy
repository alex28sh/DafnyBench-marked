method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  M0();
  M1();
  EqualityOfStrings0();
  EqualityOfStrings1();
// impl-end
}

method M0()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert {"x", "y", "z"} - {"y"} == {"x", "z"};
  // assert-end

// impl-end
}

method M1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var n :| ("R", n) in {("R", 2), ("P", 1)};
  // assert-start
  assert n == 2;
  // assert-end

  print n, "\n";
// impl-end
}

method EqualityOfStrings0()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert "a" != "b";
  // assert-end

// impl-end
}

method EqualityOfStrings1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert "a" + "b" == "ab";
  // assert-end

// impl-end
}

method M2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert !([0, 0] in {[0, 2], [1, 2]});
  // assert-end

// impl-end
}

method M3()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert [0, 0] !in {[0, 2], [1, 2]};
  // assert-end

// impl-end
}
