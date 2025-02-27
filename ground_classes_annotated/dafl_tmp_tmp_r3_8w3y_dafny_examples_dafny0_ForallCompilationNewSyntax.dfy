// dafl_tmp_tmp_r3_8w3y_dafny_examples_dafny0_ForallCompilationNewSyntax.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var c := new MyClass;
  c.arr := new int[10, 20];
  c.K0(3, 12);
  c.K1(3, 12);
  c.K2(3, 12);
  c.K3(3, 12);
  c.K4(12);
  c.M();
  c.N();
  c.P();
  c.Q();
// impl-end
}

class MyClass {
  var arr: array2<int>

  method K0(i: int, j: int)
    // pre-conditions-start
    requires 0 <= i < this.arr.Length0 && 0 <= j < this.arr.Length1
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr
    // post-conditions-end
  {
  // impl-start
    forall k | k in {-3, 4} {
      this.arr[i, j] := 50;
    }
  // impl-end
  }

  method K1(i: int, j: int)
    // pre-conditions-start
    requires 0 <= i < this.arr.Length0 && 0 <= j < this.arr.Length1
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    forall k | k in {} {
      this.arr[i, j] := k;
    }
  // impl-end
  }

  method K2(i: int, j: int)
    // pre-conditions-start
    requires 0 <= i < this.arr.Length0 && 0 <= j < this.arr.Length1
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr
    // post-conditions-end
  {
  // impl-start
    forall k | k in {-3, 4} {
    }
  // impl-end
  }

  method K3(i: int, j: int)
    // pre-conditions-start
    requires 0 <= i < this.arr.Length0 && 0 <= j < this.arr.Length1
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr
    // post-conditions-end
  {
  // impl-start
    forall k: nat | k in {-3, 4} && k <= i {
      this.arr[k, j] := 50;
    }
  // impl-end
  }

  method K4(j: int)
    // pre-conditions-start
    requires 0 <= j < this.arr.Length1
    // pre-conditions-end
    // post-conditions-start
    modifies this.arr
    // post-conditions-end
  {
  // impl-start
    forall i, k: nat | 0 <= i < this.arr.Length0 && k in {-3, 4} {
      this.arr[i, j] := k;
    }
  // impl-end
  }

  method M()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var ar := new int[3, 3];
    var S: set<int> := {2, 0};
    forall k | k in S {
      ar[k, 1] := 0;
    }
    forall k, j | k in S && j in S {
      ar[k, j] := 0;
    }
  // impl-end
  }

  method N()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var ar := new int[3, 3];
    ar[2, 2] := 0;
  // impl-end
  }

  method P()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var ar := new int[3];
    var prev := ar[..];
    var S: set<int> := {};
    forall k | k in S {
      ar[k] := 0;
    }
    // assert-start
    assert ar[..] == prev;
    // assert-end

  // impl-end
  }

  method Q()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    var ar := new int[3, 3];
    var S: set<int> := {1, 2};
    forall k | k in S {
      ar[0, 0] := 0;
    }
    // assert-start
    assert ar[0, 0] == 0;
    // assert-end

  // impl-end
  }
}
