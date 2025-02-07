method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var tree := BuildBST([-2, 8, 3, 9, 2, -7, 0]);
  PrintTreeNumbersInorder(tree);
// impl-end
}

method PrintTreeNumbersInorder(t: Tree)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  match t {
    case {:split false} Empty =>
    case {:split false} Node(n, l, r) =>
      PrintTreeNumbersInorder(l);
      print n;
      print "\n";
      PrintTreeNumbersInorder(r);
  }
// impl-end
}

function NumbersInTree(t: Tree): set<int>
{
  NumbersInSequence(Inorder(t))
}
// pure-end

function NumbersInSequence(q: seq<int>): set<int>
{
  set x | x in q
}
// pure-end

function BST(t: Tree): bool
{
  Ascending(Inorder(t))
}
// pure-end

function Inorder(t: Tree): seq<int>
{
  match t {
    case Empty =>
      []
    case Node(n', nt1, nt2) =>
      Inorder(nt1) + [n'] + Inorder(nt2)
  }
}
// pure-end

function Ascending(q: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |q| ==>
      q[i] < q[j]
}
// pure-end

function NoDuplicates(q: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |q| ==>
      q[i] != q[j]
}
// pure-end

method BuildBST(q: seq<int>) returns (t: Tree)
  // pre-conditions-start
  requires NoDuplicates(q)
  // pre-conditions-end
  // post-conditions-start
  ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
  // post-conditions-end
{
// impl-start
  t := Empty;
  for i := 0 to |q|
    // invariants-start

    invariant BST(t)
    invariant NumbersInTree(t) == NumbersInSequence(q[..i])
    // invariants-end

  {
    t := InsertBST(t, q[i]);
  }
// impl-end
}

method InsertBST(t0: Tree, x: int) returns (t: Tree)
  // pre-conditions-start
  requires BST(t0) && x !in NumbersInTree(t0)
  // pre-conditions-end
  // post-conditions-start
  ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0) + {x}
  // post-conditions-end
{
// impl-start
  match t0 {
    case {:split false} Empty =>
      t := Node(x, Empty, Empty);
    case {:split false} Node(i, left, right) =>
      {
        var tmp: Tree := Empty;
        if x < i {
          // assert-start
          LemmaBinarySearchSubtree(i, left, right);
          // assert-end

          tmp := InsertBST(left, x);
          t := Node(i, tmp, right);
          ghost var right_nums := Inorder(right);
          ghost var left_nums := Inorder(left);
          ghost var all_nums := Inorder(t0);
          // assert-start
          assert all_nums == left_nums + [i] + right_nums;
          // assert-end

          // assert-start
          assert all_nums[|left_nums|] == i;
          // assert-end

          // assert-start
          assert all_nums[|left_nums| + 1..] == right_nums;
          // assert-end

          // assert-start
          assert Ascending(right_nums);
          // assert-end

          // assert-start
          assert Ascending(left_nums);
          // assert-end

          // assert-start
          assert Ascending(left_nums + [i] + right_nums);
          // assert-end

          // assert-start
          assert forall j, k :: |left_nums| < j < k < |all_nums| ==> x < i < all_nums[j] < all_nums[k];
          // assert-end

          ghost var new_all_nums := Inorder(t);
          ghost var new_left_nums := Inorder(tmp);
          // assert-start
          assert new_all_nums == new_left_nums + [i] + right_nums;
          // assert-end

          // assert-start
          assert Ascending([i] + right_nums);
          // assert-end

          // assert-start
          assert Ascending(new_left_nums);
          // assert-end

          // assert-start
          assert NumbersInSequence(new_left_nums) == NumbersInSequence(left_nums) + {x};
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |all_nums| ==> all_nums[j] < all_nums[k];
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |left_nums| ==> all_nums[j] < all_nums[k] < all_nums[|left_nums|];
          // assert-end

          // assert-start
          assert all_nums[|left_nums|] == i;
          // assert-end

          // assert-start
          assert left_nums == all_nums[..|left_nums|];
          // assert-end

          // assert-start
          assert NumbersInSequence(new_left_nums) == NumbersInSequence(all_nums[..|left_nums|]) + {x};
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |left_nums| ==> left_nums[j] < left_nums[k] < i;
          // assert-end

          // assert-start
          assert x < i;
          // assert-end

          // assert-start
          assert forall j :: j in NumbersInSequence(all_nums[..|left_nums|]) ==> j < i;
          // assert-end

          // assert-start
          assert forall j :: j in NumbersInSequence(all_nums[..|left_nums|]) + {x} ==> j < i;
          // assert-end

          // assert-start
          assert forall j :: j in NumbersInSequence(new_left_nums) ==> j < i;
          // assert-end

          // assert-start
          assert forall j :: j in NumbersInSequence(new_left_nums) <==> j in new_left_nums;
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |new_left_nums| ==> new_left_nums[j] < new_left_nums[k];
          // assert-end

          // assert-start
          assert x < i;
          // assert-end

          // assert-start
          lemma_all_small(new_left_nums, i);
          // assert-end

          // assert-start
          assert forall j :: 0 <= j < |new_left_nums| ==> new_left_nums[j] < i;
          // assert-end

          // assert-start
          assert Ascending(new_left_nums + [i]);
          // assert-end

          // assert-start
          assert Ascending(Inorder(t));
          // assert-end

          // assert-start
          assert BST(t);
          // assert-end

        } else {
          // assert-start
          LemmaBinarySearchSubtree(i, left, right);
          // assert-end

          tmp := InsertBST(right, x);
          t := Node(i, left, tmp);
          ghost var right_nums := Inorder(right);
          ghost var left_nums := Inorder(left);
          ghost var all_nums := Inorder(t0);
          // assert-start
          assert all_nums == left_nums + [i] + right_nums;
          // assert-end

          // assert-start
          assert all_nums[|left_nums|] == i;
          // assert-end

          // assert-start
          assert all_nums[|left_nums| + 1..] == right_nums;
          // assert-end

          // assert-start
          assert Ascending(right_nums);
          // assert-end

          // assert-start
          assert Ascending(left_nums);
          // assert-end

          // assert-start
          assert Ascending(left_nums + [i] + right_nums);
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |left_nums| ==> all_nums[j] < all_nums[k] < i < x;
          // assert-end

          ghost var new_all_nums := Inorder(t);
          ghost var new_right_nums := Inorder(tmp);
          // assert-start
          assert new_all_nums == left_nums + [i] + new_right_nums;
          // assert-end

          // assert-start
          assert Ascending(left_nums + [i]);
          // assert-end

          // assert-start
          assert Ascending(new_right_nums);
          // assert-end

          // assert-start
          assert NumbersInSequence(new_right_nums) == NumbersInSequence(right_nums) + {x};
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |all_nums| ==> all_nums[j] < all_nums[k];
          // assert-end

          // assert-start
          assert forall j, k :: |left_nums| < j < k < |all_nums| ==> all_nums[|left_nums|] < all_nums[j] < all_nums[k];
          // assert-end

          // assert-start
          assert all_nums[|left_nums|] == i;
          // assert-end

          // assert-start
          assert left_nums == all_nums[..|left_nums|];
          // assert-end

          // assert-start
          assert NumbersInSequence(new_right_nums) == NumbersInSequence(all_nums[|left_nums| + 1..]) + {x};
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |right_nums| ==> i < right_nums[j] < right_nums[k];
          // assert-end

          // assert-start
          assert x > i;
          // assert-end

          // assert-start
          assert forall j :: j in NumbersInSequence(new_right_nums) ==> j > i;
          // assert-end

          // assert-start
          assert forall j :: j in NumbersInSequence(new_right_nums) <==> j in new_right_nums;
          // assert-end

          // assert-start
          assert forall j, k :: 0 <= j < k < |new_right_nums| ==> new_right_nums[j] < new_right_nums[k];
          // assert-end

          // assert-start
          assert x > i;
          // assert-end

          // assert-start
          lemma_all_big(new_right_nums, i);
          // assert-end

          // assert-start
          assert forall j :: 0 <= j < |new_right_nums| ==> new_right_nums[j] > i;
          // assert-end

          // assert-start
          assert Ascending(Inorder(t));
          // assert-end

          // assert-start
          assert BST(t);
          // assert-end

        }
      }
  }
// impl-end
}

lemma LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
  // pre-conditions-start
  requires BST(Node(n, left, right))
  // pre-conditions-end
  // post-conditions-start
  ensures BST(left) && BST(right)
  // post-conditions-end
{
// impl-start
  assert Ascending(Inorder(Node(n, left, right)));
  var qleft, qright := Inorder(left), Inorder(right);
  var q := qleft + [n] + qright;
  assert q == Inorder(Node(n, left, right));
  assert Ascending(qleft + [n] + qright);
  assert Ascending(qleft) by {
    LemmaAscendingSubsequence(q, qleft, 0);
  }
  assert Ascending(qright) by {
    LemmaAscendingSubsequence(q, qright, |qleft| + 1);
  }
// impl-end
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
  // pre-conditions-start
  requires i <= |q1| - |q2| && q2 == q1[i .. i + |q2|]
  requires Ascending(q1)
  // pre-conditions-end
  // post-conditions-start
  ensures Ascending(q2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma {:verify true} lemma_all_small(q: seq<int>, i: int)
  // pre-conditions-start
  requires forall k :: k in NumbersInSequence(q) ==> k < i
  requires forall k :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
  // pre-conditions-end
  // post-conditions-start
  ensures forall j :: 0 <= j < |q| ==> q[j] < i
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma {:verify true} lemma_all_big(q: seq<int>, i: int)
  // pre-conditions-start
  requires forall k :: k in NumbersInSequence(q) ==> k > i
  requires forall k :: 0 <= k < |q| ==> q[k] in NumbersInSequence(q)
  // pre-conditions-end
  // post-conditions-start
  ensures forall j :: 0 <= j < |q| ==> q[j] > i
  // post-conditions-end
{
// impl-start
// impl-end
}

datatype Tree = Empty | Node(int, Tree, Tree)
