// stunning-palm-tree_tmp_tmpr84c2iwh_ch10.dfy


module PQueue {
  function Empty(): PQueue
  {
    Leaf
  }
  // pure-end

  predicate IsEmpty(pq: PQueue)
  {
    pq == Leaf
  }
  // pure-end

  function Insert(pq: PQueue, y: int): PQueue
  {
    match pq
    case Leaf =>
      Node(y, Leaf, Leaf)
    case Node(x, left, right) =>
      if y < x then
        Node(y, Insert(right, x), left)
      else
        Node(x, Insert(right, y), left)
  }
  // pure-end

  function RemoveMin(pq: PQueue): (int, PQueue)
    requires Valid(pq) && !IsEmpty(pq)
  {
    var Node(x, left, right) := pq;
    (x, DeleteMin(pq))
  }
  // pure-end

  function DeleteMin(pq: PQueue): PQueue
    requires IsBalanced(pq) && !IsEmpty(pq)
  {
    if pq.right.Leaf? then
      pq.left
    else if pq.left.x <= pq.right.x then
      Node(pq.left.x, pq.right, DeleteMin(pq.left))
    else
      Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
  }
  // pure-end

  function ReplaceRoot(pq: PQueue, r: int): PQueue
    requires !IsEmpty(pq)
  {
    if pq.left.Leaf? || (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x)) then
      Node(r, pq.left, pq.right)
    else if pq.right.Leaf? then
      Node(pq.left.x, Node(r, Leaf, Leaf), Leaf)
    else if pq.left.x < pq.right.x then
      Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right)
    else
      Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r))
  }
  // pure-end

  ghost function Elements(pq: PQueue): multiset<int>
  {
    match pq
    case Leaf =>
      multiset{}
    case Node(x, left, right) =>
      multiset{x} + Elements(left) + Elements(right)
  }
  // pure-end

  ghost predicate Valid(pq: PQueue)
  {
    IsBinaryHeap(pq) &&
    IsBalanced(pq)
  }
  // pure-end

  ghost predicate IsBinaryHeap(pq: PQueue)
  {
    match pq
    case Leaf =>
      true
    case Node(x, left, right) =>
      IsBinaryHeap(left) &&
      IsBinaryHeap(right) &&
      (left.Leaf? || x <= left.x) &&
      (right.Leaf? || x <= right.x)
  }
  // pure-end

  ghost predicate IsBalanced(pq: PQueue)
  {
    match pq
    case Leaf =>
      true
    case Node(_ /* _v0 */, left, right) =>
      IsBalanced(left) &&
      IsBalanced(right) &&
      var L, R := |Elements(left)|, |Elements(right)|; L == R || L == R + 1
  }
  // pure-end

  lemma {:induction false} BinaryHeapStoresMin(pq: PQueue, y: int)
    // pre-conditions-start
    requires IsBinaryHeap(pq) && y in Elements(pq)
    // pre-conditions-end
    // post-conditions-start
    ensures pq.x <= y
    // post-conditions-end
  {
  // impl-start
    if pq.Node? {
      assert y in Elements(pq) ==> y == pq.x || y in Elements(pq.left) || y in Elements(pq.right);
      if y == pq.x {
        assert pq.x <= y;
      } else if y in Elements(pq.left) {
        assert pq.x <= pq.left.x;
        BinaryHeapStoresMin(pq.left, y);
        assert pq.x <= y;
      } else if y in Elements(pq.right) {
        assert pq.x <= pq.right.x;
        BinaryHeapStoresMin(pq.right, y);
        assert pq.x <= y;
      }
    }
  // impl-end
  }

  lemma EmptyCorrect()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Valid(Empty()) && Elements(Empty()) == multiset{}
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma IsEmptyCorrect(pq: PQueue)
    // pre-conditions-start
    requires Valid(pq)
    // pre-conditions-end
    // post-conditions-start
    ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    // post-conditions-end
  {
  // impl-start
    if Elements(pq) == multiset{} {
      assert pq.Leaf?;
    }
  // impl-end
  }

  lemma InsertCorrect(pq: PQueue, y: int)
    // pre-conditions-start
    requires Valid(pq)
    // pre-conditions-end
    // post-conditions-start
    ensures var pq' := Insert(pq, y); Valid(pq') && Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  lemma RemoveMinCorrect(pq: PQueue)
    // pre-conditions-start
    requires Valid(pq)
    requires !IsEmpty(pq)
    // pre-conditions-end
    // post-conditions-start
    ensures var (y, pq') := RemoveMin(pq); Elements(pq) == Elements(pq') + multiset{y} && IsMin(y, Elements(pq)) && Valid(pq')
    // post-conditions-end
  {
  // impl-start
    DeleteMinCorrect(pq);
  // impl-end
  }

  lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} DeleteMinCorrect(pq: PQueue)
    // pre-conditions-start
    requires Valid(pq) && !IsEmpty(pq)
    // pre-conditions-end
    // post-conditions-start
    ensures var pq' := DeleteMin(pq); Valid(pq') && Elements(pq') + multiset{pq.x} == Elements(pq) && |Elements(pq')| == |Elements(pq)| - 1
    // post-conditions-end
  {
  // impl-start
    if pq.left.Leaf? || pq.right.Leaf? {
    } else if pq.left.x <= pq.right.x {
      DeleteMinCorrect(pq.left);
    } else {
      var left, right := ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left);
      var pq' := Node(pq.right.x, left, right);
      assert pq' == DeleteMin(pq);
      calc {
        Elements(pq') + multiset{pq.x};
      ==
        multiset{pq.right.x} + Elements(left) + Elements(right) + multiset{pq.x};
      ==
        multiset{pq.right.x} + Elements(left) + Elements(right) + multiset{pq.x};
      ==
        {
          ReplaceRootCorrect(pq.right, pq.left.x);
          assert multiset{pq.right.x} + Elements(left) == Elements(pq.right) + multiset{pq.left.x};
        }
        Elements(pq.right) + multiset{pq.left.x} + Elements(right) + multiset{pq.x};
      ==
        Elements(pq.right) + multiset{pq.left.x} + Elements(DeleteMin(pq.left)) + multiset{pq.x};
      ==
        Elements(pq.right) + (multiset{pq.left.x} + Elements(DeleteMin(pq.left))) + multiset{pq.x};
      ==
        {
          DeleteMinCorrect(pq.left);
          assert multiset{pq.left.x} + Elements(DeleteMin(pq.left)) == Elements(pq.left);
        }
        Elements(pq.right) + Elements(pq.left) + multiset{pq.x};
      ==
        multiset{pq.x} + Elements(pq.right) + Elements(pq.left);
      ==
        Elements(pq);
      }
      DeleteMinCorrect(pq.left);
      assert Valid(right);
      ReplaceRootCorrect(pq.right, pq.left.x);
      assert Valid(left);
      assert pq.left.x in Elements(left);
      assert pq.right.x <= pq.left.x;
      BinaryHeapStoresMin(pq.left, pq.left.x);
      BinaryHeapStoresMin(pq.right, pq.right.x);
      assert pq.right.x <= left.x;
      assert right.Leaf? || pq.right.x <= right.x;
      assert IsBinaryHeap(pq');
    }
  // impl-end
  }

  lemma {:induction false} {:rlimit 1000} {:vcs_split_on_every_assert} ReplaceRootCorrect(pq: PQueue, r: int)
    // pre-conditions-start
    requires Valid(pq) && !IsEmpty(pq)
    // pre-conditions-end
    // post-conditions-start
    ensures var pq' := ReplaceRoot(pq, r); Valid(pq') && r in Elements(pq') && |Elements(pq')| == |Elements(pq)| && Elements(pq) + multiset{r} == Elements(pq') + multiset{pq.x}
    // post-conditions-end
  {
  // impl-start
    var pq' := ReplaceRoot(pq, r);
    var left, right := pq'.left, pq'.right;
    if pq.left.Leaf? || (r <= pq.left.x && (pq.right.Leaf? || r <= pq.right.x)) {
      assert Valid(pq');
      assert |Elements(pq')| == |Elements(pq)|;
    } else if pq.right.Leaf? {
    } else if pq.left.x < pq.right.x {
      assert pq.left.Node? && pq.right.Node?;
      assert pq.left.x < r || pq.right.x < r;
      assert pq' == Node(pq.left.x, ReplaceRoot(pq.left, r), pq.right);
      ReplaceRootCorrect(pq.left, r);
      assert Valid(pq');
      calc {
        Elements(pq') + multiset{pq.x};
      ==
        multiset{pq.left.x} + Elements(ReplaceRoot(pq.left, r)) + Elements(pq.right) + multiset{pq.x};
      ==
        {
          ReplaceRootCorrect(pq.left, r);
        }
        Elements(pq.left) + multiset{r} + Elements(pq.right) + multiset{pq.x};
      ==
        Elements(pq) + multiset{r};
      }
    } else {
      assert pq' == Node(pq.right.x, pq.left, ReplaceRoot(pq.right, r));
      ReplaceRootCorrect(pq.right, r);
      assert Valid(pq');
      calc {
        Elements(pq') + multiset{pq.x};
      ==
        multiset{pq.right.x} + Elements(pq.left) + Elements(ReplaceRoot(pq.right, r)) + multiset{pq.x};
      ==
        Elements(pq.left) + (Elements(ReplaceRoot(pq.right, r)) + multiset{pq.right.x}) + multiset{pq.x};
      ==
        {
          ReplaceRootCorrect(pq.right, r);
        }
        Elements(pq.left) + multiset{r} + Elements(pq.right) + multiset{pq.x};
      ==
        Elements(pq) + multiset{r};
      }
    }
  // impl-end
  }

  ghost predicate IsMin(y: int, s: multiset<int>)
  {
    y in s &&
    forall x :: 
      x in s ==>
        y <= x
  }
  // pure-end

  type PQueue = BraunTree

  datatype BraunTree = Leaf | Node(x: int, left: BraunTree, right: BraunTree)
}

module PQueueClient {
  method Client()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var pq := PQ.Empty();
    // assert-start
    PQ.EmptyCorrect();
    // assert-end

    // assert-start
    assert PQ.Elements(pq) == multiset{};
    // assert-end

    // assert-start
    assert PQ.Valid(pq);
    // assert-end

    // assert-start
    PQ.InsertCorrect(pq, 1);
    // assert-end

    var pq1 := PQ.Insert(pq, 1);
    // assert-start
    assert 1 in PQ.Elements(pq1);
    // assert-end

    // assert-start
    PQ.InsertCorrect(pq1, 2);
    // assert-end

    var pq2 := PQ.Insert(pq1, 2);
    // assert-start
    assert 2 in PQ.Elements(pq2);
    // assert-end

    // assert-start
    PQ.IsEmptyCorrect(pq2);
    // assert-end

    // assert-start
    PQ.RemoveMinCorrect(pq2);
    // assert-end

    var (m, pq3) := PQ.RemoveMin(pq2);
    // assert-start
    PQ.IsEmptyCorrect(pq3);
    // assert-end

    // assert-start
    PQ.RemoveMinCorrect(pq3);
    // assert-end

    var (n, pq4) := PQ.RemoveMin(pq3);
    // assert-start
    PQ.IsEmptyCorrect(pq4);
    // assert-end

    // assert-start
    assert PQ.IsEmpty(pq4);
    // assert-end

    // assert-start
    assert m <= n;
    // assert-end

  // impl-end
  }

  import PQ = PQueue
}
