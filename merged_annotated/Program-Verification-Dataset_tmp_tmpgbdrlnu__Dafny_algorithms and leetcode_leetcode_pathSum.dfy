function TreeSeq(root: TreeNode): seq<TreeNode>
{
  match root {
    case Nil =>
      [Nil]
    case Cons(val, left, right) =>
      [root] + TreeSeq(left) + TreeSeq(right)
  }
}
// pure-end

function TreeSet(root: TreeNode): set<TreeNode>
{
  match root {
    case Nil =>
      {Nil}
    case Cons(val, left, right) =>
      TreeSet(left) + {root} + TreeSet(right)
  }
}
// pure-end

function isPath(paths: seq<TreeNode>, root: TreeNode): bool
{
  if |paths| == 0 then
    false
  else
    match paths[0] { case Nil => false case Cons(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right)) }
}
// pure-end

function pathSum(paths: seq<TreeNode>): nat
{
  if |paths| == 0 then
    0
  else
    match paths[0] { case Nil => 0 case Cons(val, left, right) => val + pathSum(paths[1..]) }
}
// pure-end

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
  // post-conditions-end
{
// impl-start
  if root == Nil {
    return false;
  }
  if root.val - targetSum == 0 && root.left == Nil && root.right == Nil {
    // assert-start
    assert isPath([root], root) && pathSum([root]) == targetSum;
    // assert-end

    return true;
  }
  var leftPath := hasPathSum(root.left, targetSum - root.val);
  var rightPath := hasPathSum(root.right, targetSum - root.val);
  if leftPath {
    ghost var p: seq<TreeNode> :| isPath(p, root.left) && pathSum(p) == targetSum - root.val;
    // assert-start
    assert isPath([root] + p, root) && pathSum([root] + p) == targetSum;
    // assert-end

  }
  if rightPath {
    ghost var p: seq<TreeNode> :| isPath(p, root.right) && pathSum(p) == targetSum - root.val;
    // assert-start
    assert isPath([root] + p, root) && pathSum([root] + p) == targetSum;
    // assert-end

  }
  return leftPath || rightPath;
// impl-end
}

method Test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var c := Cons(3, Nil, Nil);
  var b := Cons(2, c, Nil);
  var a := Cons(1, b, Nil);
  // assert-start
  assert isPath([a], a);
  // assert-end

  // assert-start
  assert a.left == b;
  // assert-end

  // assert-start
  assert isPath([a, b], a);
  // assert-end

  // assert-start
  assert isPath([a, b, c], a);
  // assert-end

// impl-end
}

datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)
