method foo()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  bar();
  // assert-start
  assert false;
  // assert-end

// impl-end
}

method bar()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures false
  // post-conditions-end
