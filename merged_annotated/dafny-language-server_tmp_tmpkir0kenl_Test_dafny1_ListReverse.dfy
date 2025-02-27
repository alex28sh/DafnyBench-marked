// dafny-language-server_tmp_tmpkir0kenl_Test_dafny1_ListReverse.dfy

class Node {
  var nxt: Node?

  method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    // pre-conditions-start
    requires x == null || x in r
    requires forall y :: y in r ==> y.nxt == null || y.nxt in r
    // pre-conditions-end
    // post-conditions-start
    modifies r
    ensures reverse == null || reverse in r
    ensures forall y :: y in r ==> y.nxt == null || y.nxt in r
    decreases *
    // post-conditions-end
  {
  // impl-start
    var current: Node? := x;
    reverse := null;
    while current != null
      // invariants-start

      invariant current == null || current in r
      invariant reverse == null || reverse in r
      invariant forall y :: y in r ==> y.nxt == null || y.nxt in r
      decreases *
      // invariants-end

    {
      var tmp := current.nxt;
      current.nxt := reverse;
      reverse := current;
      current := tmp;
    }
  // impl-end
  }
}
