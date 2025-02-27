// dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_InSetComprehension.dfy

lemma Tests<T>(t: T, uu: seq<T>) returns (z: bool)
  // pre-conditions-start
  requires 10 <= |uu| && uu[4] == t
  // pre-conditions-end
  // post-conditions-start
  ensures !z
  // post-conditions-end
{
// impl-start
  if {
    case true =>
      z := 72 in set i | 0 <= i < 10;
    case true =>
      z := -8 in set k: nat | k < 10;
    case true =>
      z := 6 in set m | 0 <= m < 10 && Even(m) :: m + 1;
    case true =>
      z := t !in set u | u in uu;
    case true =>
      z := t !in set u {:autotriggers false} | u in uu :: Id(u);
  }
// impl-end
}

lemma TestsWhereTriggersMatter<T>(t: T, uu: seq<T>) returns (z: bool)
  // pre-conditions-start
  requires 10 <= |uu| && uu[4] == t
  // pre-conditions-end
  // post-conditions-start
  ensures z
  // post-conditions-end
{
// impl-start
  if {
    case true =>
      z := 7 in set i | 0 <= i < 10;
    case true =>
      z := 8 in set k: nat | k < 10;
    case true =>
      z := 5 in set m | 0 <= m < 10 && Even(m) :: m + 1;
      assert Even(4);
    case true =>
      z := t in set u | u in uu;
    case true =>
      z := t in set u {:autotriggers false} | u in uu :: Id(u);
  }
// impl-end
}

function Id<T>(t: T): T
{
  t
}
// pure-end

predicate Even(x: int)
{
  x % 2 == 0
}
// pure-end

method UnboxedBoundVariables(si: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var iii := set x | x in si;
  var ti := si + [115];
  var jjj := set y | y in ti;
  // assert-start
  assert iii + {115} == jjj;
  // assert-end

  var nnn := set n: nat | n in si;
  if forall i :: 0 <= i < |si| ==> 0 <= si[i] {
    // assert-start
    assert nnn == iii;
    // assert-end

  }
// impl-end
}

class Container<T> {
  ghost var Contents: set<T>
  var elems: seq<T>

  method Add(t: T)
    // pre-conditions-start
    requires this.Contents == set x | x in this.elems
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Contents == set x | x in this.elems
    // post-conditions-end
  {
  // impl-start
    this.elems := this.elems + [t];
    this.Contents := this.Contents + {t};
  // impl-end
  }
}

class IntContainer {
  ghost var Contents: set<int>
  var elems: seq<int>

  method Add(t: int)
    // pre-conditions-start
    requires this.Contents == set x | x in this.elems
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Contents == set x | x in this.elems
    // post-conditions-end
  {
  // impl-start
    this.elems := this.elems + [t];
    this.Contents := this.Contents + {t};
  // impl-end
  }
}
