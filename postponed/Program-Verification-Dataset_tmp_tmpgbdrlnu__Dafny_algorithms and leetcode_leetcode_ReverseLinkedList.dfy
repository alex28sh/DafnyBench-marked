
function reverse<A>(x: seq<A>): seq<A>
{
  if x == [] then
    []
  else
    reverse(x[1..]) + [x[0]]
}
// pure-end

function nodeConcat(xs: ListNode, end: ListNode): ListNode
{
  if xs == Null then
    end
  else
    Node(xs.val, nodeConcat(xs.next, end))
}
// pure-end

function reverseList(xs: ListNode): ListNode
{
  if xs == Null then
    Null
  else
    nodeConcat(reverseList(xs.next), Node(xs.val, Null))
}
// pure-end

lemma ConcatNullIsRightIdentity(xs: ListNode)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures xs == nodeConcat(xs, Null)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ConcatNullIsLeftIdentity(xs: ListNode)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures xs == nodeConcat(Null, xs)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ConcatExtensionality(xs: ListNode)
  // pre-conditions-start
  requires xs != Null
  // pre-conditions-end
  // post-conditions-start
  ensures nodeConcat(Node(xs.val, Null), xs.next) == xs
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ConcatAssociative(xs: ListNode, ys: ListNode, zs: ListNode)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures nodeConcat(nodeConcat(xs, ys), zs) == nodeConcat(xs, nodeConcat(ys, zs))
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma reverseSingleList(xs: ListNode)
  // pre-conditions-start
  requires xs != Null
  requires xs.next == Null
  // pre-conditions-end
  // post-conditions-start
  ensures reverseList(xs) == xs
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma {:verify true} ConcatReverseList(xs: ListNode, ys: ListNode)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures reverseList(nodeConcat(xs, ys)) == nodeConcat(reverseList(ys), reverseList(xs))
  decreases xs
  // post-conditions-end
{
// impl-start
  if xs == Null {
    calc {
      reverseList(nodeConcat(xs, ys));
    ==
      {
        ConcatNullIsLeftIdentity(ys);
      }
      reverseList(ys);
    ==
      {
        ConcatNullIsRightIdentity(reverseList(ys));
      }
      nodeConcat(reverseList(ys), Null);
      nodeConcat(reverseList(ys), xs);
      nodeConcat(reverseList(ys), reverseList(xs));
    }
  } else {
    var x := Node(xs.val, Null);
    calc {
      reverseList(nodeConcat(xs, ys));
      reverseList(nodeConcat(nodeConcat(x, xs.next), ys));
    ==
      {
        ConcatAssociative(x, xs.next, ys);
      }
      reverseList(nodeConcat(x, nodeConcat(xs.next, ys)));
      nodeConcat(reverseList(nodeConcat(xs.next, ys)), x);
    ==
      {
        ConcatReverseList(xs.next, ys);
      }
      nodeConcat(nodeConcat(reverseList(ys), reverseList(xs.next)), x);
    ==
      {
        ConcatAssociative(reverseList(ys), reverseList(xs.next), x);
      }
      nodeConcat(reverseList(ys), nodeConcat(reverseList(xs.next), x));
      nodeConcat(reverseList(ys), reverseList(xs));
    }
  }
// impl-end
}

lemma reverseReverseListIsIdempotent(xs: ListNode)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures reverseList(reverseList(xs)) == xs
  // post-conditions-end
{
// impl-start
  if xs == Null {
  } else {
    var x := Node(xs.val, Null);
    calc {
      reverseList(reverseList(xs));
      reverseList(reverseList(nodeConcat(x, xs.next)));
    ==
      {
        ConcatReverseList(x, xs.next);
      }
      reverseList(nodeConcat(reverseList(xs.next), reverseList(x)));
      reverseList(nodeConcat(reverseList(xs.next), x));
    ==
      {
        ConcatReverseList(reverseList(xs.next), x);
      }
      nodeConcat(reverseList(x), reverseList(reverseList(xs.next)));
      nodeConcat(x, reverseList(reverseList(xs.next)));
      nodeConcat(x, xs.next);
      xs;
    }
  }
// impl-end
}

lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(xs) == multiset(reverse(xs))
  // post-conditions-end
{
// impl-start
  if xs == [] {
  } else {
    var x := xs[0];
    assert xs == [x] + xs[1..];
    assert multiset(xs) == multiset([x]) + multiset(xs[1..]);
    assert reverse(xs) == reverse(xs[1..]) + [x];
    reversePreservesMultiset(xs[1..]);
    assert multiset(xs[1..]) == multiset(reverse(xs[1..]));
  }
// impl-end
}

lemma reversePreservesLength<A>(xs: seq<A>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |xs| == |reverse(xs)|
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lastReverseIsFirst<A>(xs: seq<A>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures xs[0] == reverse(xs)[|reverse(xs)| - 1]
  // post-conditions-end
{
// impl-start
  reversePreservesLength(xs);
  assert |xs| == |reverse(xs)|;
// impl-end
}

lemma firstReverseIsLast<A>(xs: seq<A>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(xs)[0] == xs[|xs| - 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
  // post-conditions-end
{
// impl-start
  if |xs| == 0 {
    assert xs + ys == ys;
  } else {
    assert xs + ys == [xs[0]] + (xs[1..] + ys);
  }
// impl-end
}

lemma reverseRest<A>(xs: seq<A>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(xs) == [xs[|xs| - 1]] + reverse(xs[0 .. |xs| - 1])
  // post-conditions-end
{
// impl-start
  firstReverseIsLast(xs);
  assert xs == xs[0 .. |xs| - 1] + [xs[|xs| - 1]];
  assert reverse(xs)[0] == xs[|xs| - 1];
  assert reverse(xs) == [xs[|xs| - 1]] + reverse(xs)[1..];
  calc {
    reverse(xs);
    reverse(xs[0 .. |xs| - 1] + [xs[|xs| - 1]]);
  ==
    {
      ReverseConcat(xs[0 .. |xs| - 1], [xs[|xs| - 1]]);
    }
    reverse([xs[|xs| - 1]]) + reverse(xs[0 .. |xs| - 1]);
  }
// impl-end
}

lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
  // pre-conditions-start
  requires |xs| == |ys|
  requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
  // pre-conditions-end
  // post-conditions-start
  ensures xs == ys
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ReverseIndexAll<T>(xs: seq<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |reverse(xs)| == |xs|
  ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ReverseIndex<T>(xs: seq<T>, i: int)
  // pre-conditions-start
  requires 0 <= i < |xs|
  // pre-conditions-end
  // post-conditions-start
  ensures |reverse(xs)| == |xs|
  ensures reverse(xs)[i] == xs[|xs| - i - 1]
  // post-conditions-end
{
// impl-start
  ReverseIndexAll(xs);
  assert forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1];
// impl-end
}

lemma ReverseSingle<A>(xs: seq<A>)
  // pre-conditions-start
  requires |xs| == 1
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(xs) == xs
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma reverseReverseIdempotent<A>(xs: seq<A>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(reverse(xs)) == xs
  // post-conditions-end
{
// impl-start
  if xs == [] {
  } else {
    calc {
      reverse(reverse(xs));
      reverse(reverse([xs[0]] + xs[1..]));
    ==
      {
        ReverseConcat([xs[0]], xs[1..]);
      }
      reverse(reverse(xs[1..]) + reverse([xs[0]]));
    ==
      {
        ReverseSingle([xs[0]]);
      }
      reverse(reverse(xs[1..]) + [xs[0]]);
    ==
      {
        ReverseConcat(reverse(xs[1..]), [xs[0]]);
      }
      reverse([xs[0]]) + reverse(reverse(xs[1..]));
      [xs[0]] + reverse(reverse(xs[1..]));
    ==
      {
        reverseReverseIdempotent(xs[1..]);
      }
      xs;
    }
  }
// impl-end
}

method test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var cycle := Node(1, Null);
  var next := Node(2, cycle);
// impl-end
}

datatype ListNode = Null | Node(val: nat, next: ListNode)
