
function stepSum(xs: seq<Steps>): nat
{
  if xs == [] then
    0
  else
    match xs[0] { case One => 1 case Two => 2 } + stepSum(xs[1..])
}
// pure-end

ghost predicate stepEndsAt(xs: seq<Steps>, n: nat)
{
  stepSum(xs) == n
}
// pure-end

ghost predicate allEndAtN(ss: set<seq<Steps>>, n: nat)
{
  forall xs :: 
    xs in ss ==>
      stepEndsAt(xs, n)
}
// pure-end

lemma stepBaseZero()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists ss: set<seq<Steps>> :: allEndAtN(ss, 0) && |ss| == 0
  // post-conditions-end
{
// impl-start
  assert allEndAtN({[]}, 0);
// impl-end
}

lemma stepBaseOne()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists ss: set<seq<Steps>> :: allEndAtN(ss, 1) && |ss| == 1
  // post-conditions-end
{
// impl-start
  assert allEndAtN({[One]}, 1);
// impl-end
}

lemma stepBaseTwo()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists ss: set<seq<Steps>> :: allEndAtN(ss, 2) && |ss| == 2
  // post-conditions-end
{
// impl-start
  assert allEndAtN({[One, One], [Two]}, 2);
// impl-end
}

ghost function plusOne(x: seq<Steps>): seq<Steps>
{
  [One] + x
}
// pure-end

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>>
  ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
  ensures addOne(ss) == set x | x in ss :: plusOne(x)
{
  set x | x in ss :: plusOne(x)
}
// pure-end

lemma SeqsNotEqualImplication<T>(xs: seq<T>, ys: seq<T>, someT: T)
  // pre-conditions-start
  requires xs != ys
  // pre-conditions-end
  // post-conditions-start
  ensures (exists i: nat :: i < |xs| && i < |ys| && xs[i] != ys[i]) || |xs| < |ys| || |ys| < |xs|
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
  // pre-conditions-start
  requires xs != ys
  // pre-conditions-end
  // post-conditions-start
  ensures [someT] + xs != [someT] + ys
  // post-conditions-end
{
// impl-start
  if |xs| < |ys| {
  } else if |ys| > |xs| {
  } else if i: nat :| i < |xs| && i < |ys| && xs[i] != ys[i] {
    assert ([someT] + xs)[i + 1] != ([someT] + ys)[i + 1];
  }
// impl-end
}

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
  // pre-conditions-start
  requires x !in ss
  // pre-conditions-end
  // post-conditions-start
  ensures plusOne(x) !in addOne(ss)
  // post-conditions-end
{
// impl-start
  if x == [] {
    assert [] !in ss;
    assert [One] + [] !in addOne(ss);
  }
  if plusOne(x) in addOne(ss) {
    forall y | y in ss
      ensures y != x
      ensures plusOne(y) in addOne(ss)
      ensures plusOne(y) != plusOne(x)
    {
      UnequalSeqs(x, y, One);
      assert plusOne(y) != [One] + x;
    }
    assert false;
  }
// impl-end
}

lemma addOneSize(ss: set<seq<Steps>>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |addOne(ss)| == |ss|
  // post-conditions-end
{
// impl-start
  var size := |ss|;
  if x :| x in ss {
    assert |ss - {x}| == size - 1;
    addOneSize(ss - {x});
    assert |addOne(ss - {x})| == size - 1;
    assert addOne(ss) == addOne(ss - {x}) + {[One] + x};
    assert x !in ss - {x};
    plusOneNotIn(ss - {x}, x);
    assert plusOne(x) !in addOne(ss - {x});
    assert |addOne(ss)| == |addOne(ss - {x})| + |{[One] + x}|;
  } else {
  }
// impl-end
}

lemma addOneSum(ss: set<seq<Steps>>, sum: nat)
  // pre-conditions-start
  requires allEndAtN(ss, sum)
  // pre-conditions-end
  // post-conditions-start
  ensures allEndAtN(addOne(ss), sum + 1)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma endAtNPlus(ss: set<seq<Steps>>, sz: set<seq<Steps>>, sum: nat)
  // pre-conditions-start
  requires allEndAtN(ss, sum)
  requires allEndAtN(sz, sum)
  // pre-conditions-end
  // post-conditions-start
  ensures allEndAtN(ss + sz, sum)
  // post-conditions-end
{
// impl-start
// impl-end
}

ghost function plusTwo(x: seq<Steps>): seq<Steps>
{
  [Two] + x
}
// pure-end

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>>
  ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
  ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{
  set x | x in ss :: plusTwo(x)
}
// pure-end

lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
  // pre-conditions-start
  requires x !in ss
  // pre-conditions-end
  // post-conditions-start
  ensures plusTwo(x) !in addTwo(ss)
  // post-conditions-end
{
// impl-start
  if x == [] {
    assert [] !in ss;
    assert [Two] + [] !in addTwo(ss);
  }
  if plusTwo(x) in addTwo(ss) {
    forall y | y in ss
      ensures y != x
      ensures plusTwo(y) in addTwo(ss)
      ensures plusTwo(y) != plusTwo(x)
    {
      UnequalSeqs(x, y, Two);
      assert plusTwo(y) != [Two] + x;
    }
  }
// impl-end
}

lemma addTwoSize(ss: set<seq<Steps>>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |addTwo(ss)| == |ss|
  // post-conditions-end
{
// impl-start
  var size := |ss|;
  if x :| x in ss {
    addTwoSize(ss - {x});
    assert addTwo(ss) == addTwo(ss - {x}) + {[Two] + x};
    plusTwoNotIn(ss - {x}, x);
    assert |addTwo(ss)| == |addTwo(ss - {x})| + |{[Two] + x}|;
  }
// impl-end
}

lemma addTwoSum(ss: set<seq<Steps>>, sum: nat)
  // pre-conditions-start
  requires allEndAtN(ss, sum)
  // pre-conditions-end
  // post-conditions-start
  ensures allEndAtN(addTwo(ss), sum + 2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma setSizeAddition<T>(sx: set<T>, sy: set<T>, sz: set<T>)
  // pre-conditions-start
  requires sx !! sy
  requires sz == sx + sy
  // pre-conditions-end
  // post-conditions-start
  ensures |sx + sy| == |sx| + |sy|
  ensures |sz| == |sx| + |sy|
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma stepSetsAdd(i: nat, steps: array<nat>)
  // pre-conditions-start
  requires i >= 2
  requires steps.Length >= i + 1
  requires forall k: nat :: k < i ==> exists ss: set<seq<Steps>> :: steps[k] == |ss| && allEndAtN(ss, k)
  // pre-conditions-end
  // post-conditions-start
  ensures exists sp: set<seq<Steps>> :: |sp| == steps[i - 1] + steps[i - 2] && allEndAtN(sp, i)
  // post-conditions-end
{
// impl-start
  var oneStepBack :| steps[i - 1] == |oneStepBack| && allEndAtN(oneStepBack, i - 1);
  var twoStepBack :| steps[i - 2] == |twoStepBack| && allEndAtN(twoStepBack, i - 2);
  var stepForward := addOne(oneStepBack);
  var stepTwoForward := addTwo(twoStepBack);
  assert forall x :: x in stepForward ==> x[0] == One;
  addOneSize(oneStepBack);
  addTwoSize(twoStepBack);
  var sumSet := stepForward + stepTwoForward;
// impl-end
}

method climbStairs(n: nat) returns (count: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists ss: set<seq<Steps>> :: count == |ss| && allEndAtN(ss, n)
  // post-conditions-end
{
// impl-start
  var steps := new nat[n + 1];
  steps[0] := 0;
  if n > 0 {
    steps[1] := 1;
  }
  if n > 1 {
    steps[2] := 2;
  }
  // assert-start
  stepBaseZero();
  // assert-end

  // assert-start
  stepBaseOne();
  // assert-end

  // assert-start
  stepBaseTwo();
  // assert-end

  if n < 3 {
    return steps[n];
  }
  // assert-start
  assert steps[0] == 0;
  // assert-end

  // assert-start
  assert steps[1] == 1;
  // assert-end

  // assert-start
  assert steps[2] == 2;
  // assert-end

  // assert-start
  assert forall k: nat :: k < 3 ==> exists ss: set<seq<Steps>> :: steps[k] == |ss| && allEndAtN(ss, k);
  // assert-end

  var i := 3;
  while i <= n
    // invariants-start

    invariant 3 <= i <= n + 1
    invariant forall k: nat :: k < i ==> exists ss: set<seq<Steps>> :: steps[k] == |ss| && allEndAtN(ss, k)
    // invariants-end

  {
    steps[i] := steps[i - 1] + steps[i - 2];
    // assert-start
    stepSetsAdd(i, steps);
    // assert-end

    i := i + 1;
  }
  return steps[n];
// impl-end
}

method Test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var foo := [One, One, Two];
  // assert-start
  assert stepSum(foo) == 4;
  // assert-end

// impl-end
}

datatype Steps = One | Two
