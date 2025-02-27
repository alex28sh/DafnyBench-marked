// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue67.dfy

predicate Q(x: Node)
// pure-end

predicate P(x: Node)
// pure-end

method AuxMethod(y: Node)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies y
  // post-conditions-end

method MainMethod(y: Node)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies y
  // post-conditions-end
{
// impl-start
  AuxMethod(y);
  forall x | Q(x)
    ensures P(x)
  {
    // assert-start
    assume false;
    // assert-end

  }
  // assert-start
  assert forall x :: Q(x) ==> P(x);
  // assert-end

// impl-end
}

class Node { }
