method abs(x: int) returns (y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures true
  // post-conditions-end
{
// impl-start
  if x < 0 {
    y := -x;
  } else {
    y := x;
  }
// impl-end
}

method foo(x: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var y := abs(x);
// impl-end
}

method max(x: int, y: int) returns (m: int)
  // pre-conditions-start
  requires true
  // pre-conditions-end
  // post-conditions-start
  ensures true
  // post-conditions-end
{
// impl-start
  var r: int;
  if x > y {
    r := 0;
  } else {
    r := 1;
  }
  m := r;
// impl-end
}

method ex1(n: int)
  // pre-conditions-start
  requires true
  // pre-conditions-end
  // post-conditions-start
  ensures true
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < n
    // invariants-start

    invariant true
    // invariants-end

  {
    i := i + 1;
  }
// impl-end
}

method foo2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures false
  decreases *
  // post-conditions-end
{
// impl-start
  while true
    // invariants-start

    decreases *
    // invariants-end

  {
  }
  // assert-start
  assert false;
  // assert-end

// impl-end
}

method find(a: seq<int>, key: int) returns (index: int)
  // pre-conditions-start
  requires true
  // pre-conditions-end
  // post-conditions-start
  ensures true
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < |a|
    // invariants-start

    invariant true
    // invariants-end

  {
    if a[index] == key {
      return 0;
    }
    index := index + 2;
  }
  index := -10;
// impl-end
}

method isPalindrome(a: seq<char>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  return true;
// impl-end
}

function sorted(a: seq<int>): bool
{
  forall j, k :: 
    0 <= j < k < |a| ==>
      a[j] <= a[k]
}
// pure-end

method unique(a: seq<int>) returns (b: seq<int>)
  // pre-conditions-start
  requires sorted(a)
  // pre-conditions-end
  // post-conditions-start
  ensures true
  // post-conditions-end
{
// impl-start
  return a;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var r := find([], 1);
  print r, "\n";
  r := find([0, 3, 5, 7], 5);
  print r, "\n";
  var s1 := ['a'];
  var r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  s1 := [];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  s1 := ['a', 'b'];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  s1 := ['a', 'b', 'a'];
  r1 := isPalindrome(s1);
  print "is [", s1, "]", " a isPalindrome? ", r1, " \n";
  var i := [0, 1, 3, 3, 5, 5, 7];
  var s := unique(i);
  print "unique applied to ", i, " is ", s, "\n";
// impl-end
}
