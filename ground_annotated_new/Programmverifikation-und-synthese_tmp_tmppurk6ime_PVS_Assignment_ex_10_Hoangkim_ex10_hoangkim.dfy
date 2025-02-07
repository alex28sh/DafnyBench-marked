method square0(n: nat) returns (sqn: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sqn == n * n
  // post-conditions-end
{
// impl-start
  sqn := 0;
  var i := 0;
  var x;
  while i < n
    // invariants-start

    invariant i <= n && sqn == i * i
    // invariants-end

  {
    x := 2 * i + 1;
    sqn := sqn + x;
    i := i + 1;
  }
// impl-end
}

method square1(n: nat) returns (sqn: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sqn == n * n
  // post-conditions-end
{
// impl-start
  sqn := 0;
  var i := 0;
  while i < n
    // invariants-start

    invariant i <= n && sqn == i * i
    // invariants-end

  {
    var x := 2 * i + 1;
    sqn := sqn + x;
    i := i + 1;
  }
// impl-end
}

method q(x: nat, y: nat) returns (z: nat)
  // pre-conditions-start
  requires y - x > 2
  // pre-conditions-end
  // post-conditions-start
  ensures x < z * z < y
  // post-conditions-end

method strange()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 1 == 2
  // post-conditions-end
{
// impl-start
  var x := 4;
  var c: nat := q(x, 2 * x);
// impl-end
}

method test0()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x: int := *;
  // assert-start
  assume x * x < 100;
  // assert-end

  // assert-start
  assert x <= 9;
  // assert-end

// impl-end
}
