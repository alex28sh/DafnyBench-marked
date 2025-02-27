function BinarySearchTree(tree: Tree): bool
  decreases tree
{
  match tree
  case Empty =>
    true
  case Node(_ /* _v0 */, _ /* _v1 */, _ /* _v2 */) =>
    (tree.left == Empty || tree.left.value < tree.value) &&
    (tree.right == Empty || tree.right.value > tree.value) &&
    BinarySearchTree(tree.left) &&
    BinarySearchTree(tree.right) &&
    minValue(tree.right, tree.value) &&
    maxValue(tree.left, tree.value)
}
// pure-end

function maxValue(tree: Tree, max: int): bool
  decreases tree
{
  match tree
  case Empty =>
    true
  case Node(left, v, right) =>
    max > v &&
    maxValue(left, max) &&
    maxValue(right, max)
}
// pure-end

function minValue(tree: Tree, min: int): bool
  decreases tree
{
  match tree
  case Empty =>
    true
  case Node(left, v, right) =>
    min < v &&
    minValue(left, min) &&
    minValue(right, min)
}
// pure-end

method GetMin(tree: Tree) returns (res: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  match tree {
    case {:split false} Empty =>
      res := 0;
    case {:split false} Node(Empty, value, Empty) =>
      res := tree.value;
    case {:split false} Node(Empty, value, right) =>
      res := tree.value;
    case {:split false} Node(left, value, right) =>
      var minval := tree.value;
      minval := GetMin(tree.left);
      var tmp := Node(tree.left, minval, tree.right);
      res := tmp.value;
  }
// impl-end
}

method GetMax(tree: Tree) returns (res: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  match tree {
    case {:split false} Empty =>
      res := 0;
    case {:split false} Node(Empty, value, Empty) =>
      res := tree.value;
    case {:split false} Node(left, value, Empty) =>
      res := tree.value;
    case {:split false} Node(left, value, right) =>
      var minval := tree.value;
      minval := GetMax(tree.right);
      var tmp := Node(tree.left, minval, tree.right);
      res := tmp.value;
  }
// impl-end
}

method insert(tree: Tree, value: int) returns (res: Tree)
  // pre-conditions-start
  requires BinarySearchTree(tree)
  // pre-conditions-end
  // post-conditions-start
  ensures BinarySearchTree(res)
  decreases tree
  // post-conditions-end
{
// impl-start
  res := insertRecursion(tree, value);
// impl-end
}

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  // pre-conditions-start
  requires BinarySearchTree(tree)
  // pre-conditions-end
  // post-conditions-start
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
  decreases tree
  // post-conditions-end
{
// impl-start
  match tree {
    case {:split false} Empty =>
      res := Node(Empty, value, Empty);
    case {:split false} Node(_ /* _v3 */, _ /* _v4 */, _ /* _v5 */) =>
      var temp: Tree;
      if value == tree.value {
        return tree;
      }
      if value < tree.value {
        temp := insertRecursion(tree.left, value);
        res := Node(temp, tree.value, tree.right);
      } else if value > tree.value {
        temp := insertRecursion(tree.right, value);
        res := Node(tree.left, tree.value, temp);
      }
  }
// impl-end
}

method delete(tree: Tree, value: int) returns (res: Tree)
  // pre-conditions-start
  requires BinarySearchTree(tree)
  // pre-conditions-end
  // post-conditions-start
  decreases tree
  // post-conditions-end
{
// impl-start
  match tree {
    case {:split false} Empty =>
      return tree;
    case {:split false} Node(_ /* _v6 */, _ /* _v7 */, _ /* _v8 */) =>
      var temp: Tree;
      if value < tree.value {
        temp := delete(tree.left, value);
        res := Node(temp, tree.value, tree.right);
      } else if value > tree.value {
        temp := delete(tree.right, value);
        res := Node(tree.left, tree.value, temp);
      } else {
        if tree.left == Empty {
          return tree.right;
        } else if tree.right == Empty {
          return tree.left;
        }
        var minVal := GetMin(tree.right);
        temp := delete(tree.right, minVal);
        res := Node(tree.left, minVal, temp);
      }
  }
// impl-end
}

method Inorder(tree: Tree)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  match tree {
    case {:split false} Empty =>
    case {:split false} Node(left, value, right) =>
      Inorder(tree.left);
      print tree.value, ", ";
      Inorder(tree.right);
  }
// impl-end
}

method Postorder(tree: Tree)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  match tree {
    case {:split false} Empty =>
    case {:split false} Node(left, value, right) =>
      Postorder(tree.left);
      Postorder(tree.right);
      print tree.value, ", ";
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var tree := insert(Empty, 3);
  var u := insert(tree, 2);
  u := insert(u, 7);
  u := insert(u, 6);
  u := insert(u, 9);
  print "This is Inorder: ";
  Inorder(u);
  print "\n";
  print "This is Postorder: ";
  Postorder(u);
  print "\n";
  print "tree before delete: ", u, "\n";
  u := delete(u, 7);
  print "tree after delete: ", u, "\n";
  print "This is Inorder: ";
  Inorder(u);
  print "\n";
  print "This is Postorder: ";
  Postorder(u);
// impl-end
}

datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)
