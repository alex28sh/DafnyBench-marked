method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i := 2;
  var s := [1, i, 3, 4, 5];
  print |s|;
  // assert-start
  assert s[|s| - 1] == 5;
  // assert-end

  // assert-start
  assert s[|s| - 1 .. |s|] == [5];
  // assert-end

  // assert-start
  assert s[1..] == [2, 3, 4, 5];
  // assert-end

  // assert-start
  assert s[..|s| - 1] == [1, 2, 3, 4];
  // assert-end

  // assert-start
  assert s == s[0..] == s[..|s|] == s[0 .. |s|] == s[..];
  // assert-end

// impl-end
}

method foo(s: seq<int>)
  // pre-conditions-start
  requires |s| > 1
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  print s[1];
// impl-end
}
