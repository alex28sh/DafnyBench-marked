// veri-sparse_tmp_tmp15fywna6_dafny_concurrent_poc_6.dfy

function sum(s: seq<nat>): nat
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{
  if s == [] then
    0
  else
    s[0] + sum(s[1..])
}
// pure-end

lemma sum0(s: seq<nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
  // post-conditions-end
{
// impl-start
  if s == [] {
  } else {
    sum0(s[1..]);
  }
// impl-end
}

lemma sum_const(s: seq<nat>, x: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma sum_eq(s1: seq<nat>, s2: seq<nat>)
  // pre-conditions-start
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  // pre-conditions-end
  // post-conditions-start
  ensures sum(s1) == sum(s2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma sum_exept(s1: seq<nat>, s2: seq<nat>, x: nat, j: nat)
  // pre-conditions-start
  requires |s1| == |s2|
  requires j < |s1|
  requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
  requires s1[j] == s2[j] + x
  // pre-conditions-end
  // post-conditions-start
  ensures sum(s1) == sum(s2) + x
  // post-conditions-end
{
// impl-start
  if s1 == [] {
    assert j >= |s1|;
  } else {
    if j == 0 {
      assert sum(s1) == s1[0] + sum(s1[1..]);
      assert sum(s2) == s2[0] + sum(s2[1..]);
      sum_eq(s1[1..], s2[1..]);
      assert sum(s1[1..]) == sum(s2[1..]);
    } else {
      sum_exept(s1[1..], s2[1..], x, j - 1);
    }
  }
// impl-end
}

function calcRow(M: array2<int>, x: seq<int>, row: nat, start_index: nat): (product: int)
  requires M.Length1 == |x|
  requires row < M.Length0
  requires start_index <= M.Length1
  reads M
  decreases M.Length1 - start_index
{
  if start_index == M.Length1 then
    0
  else
    M[row, start_index] * x[start_index] + calcRow(M, x, row, start_index + 1)
}
// pure-end

method Run(processes: set<Process>, M: array2<int>, x: array<int>)
    returns (y: array<int>)
  // pre-conditions-start
  requires |processes| == M.Length0
  requires forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row
  requires forall p, q :: p in processes && q in processes ==> p != q
  requires forall p :: p in processes ==> 0 <= p.row < M.Length0
  requires forall p :: p in processes ==> 0 == p.curColumn
  requires forall p :: p in processes ==> p.opsLeft == M.Length1
  requires x.Length > 0
  requires M.Length0 > 0
  requires M.Length1 == x.Length
  // pre-conditions-end
  // post-conditions-start
  modifies processes, M, x
  ensures M.Length0 == y.Length
  // post-conditions-end
{
// impl-start
  var i := 0;
  y := new int[M.Length0] (i => 0);
  var leftOvers := new nat[M.Length0] (i => M.Length1);
  var mv := new MatrixVectorMultiplier(processes, M, x[..], y, leftOvers);
  while sum(leftOvers[..]) > 0 && exists p :: p in processes && p.opsLeft > 0
    // invariants-start

    invariant mv.Valid(M, x[..], y, processes, leftOvers)
    invariant forall p :: p in processes ==> y[p.row] + calcRow(M, x[..], p.row, p.curColumn) == calcRow(M, x[..], p.row, 0)
    invariant sum(leftOvers[..]) >= 0
    invariant forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row
    decreases sum(leftOvers[..])
    // invariants-end

  {
    mv.processNext(M, x[..], y, processes, leftOvers);
  }
  // assert-start
  assert sum(leftOvers[..]) == 0;
  // assert-end

  // assert-start
  assert forall i :: 0 <= i < y.Length ==> y[i] == calcRow(M, x[..], i, 0);
  // assert-end

// impl-end
}

class Process {
  var row: nat
  var curColumn: nat
  var opsLeft: nat

  constructor (init_row: nat, initOpsLeft: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.row == init_row
    ensures this.opsLeft == initOpsLeft
    ensures this.curColumn == 0
    // post-conditions-end
  {
  // impl-start
    this.row := init_row;
    this.curColumn := 0;
    this.opsLeft := initOpsLeft;
  // impl-end
  }
}

class MatrixVectorMultiplier {
  ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers: array<nat>)
    reads this, y, P, M, leftOvers
  {
    M.Length0 == y.Length &&
    M.Length1 == |x| &&
    |P| == y.Length &&
    |P| == leftOvers.Length &&
    (forall p, q :: 
      p in P &&
      q in P &&
      p != q ==>
        p.row != q.row) &&
    (forall p, q :: 
      p in P &&
      q in P ==>
        p != q) &&
    (forall p :: 
      p in P ==>
        0 <= p.row < |P|) &&
    (forall p :: 
      p in P ==>
        0 <= p.curColumn <= M.Length1) &&
    (forall p :: 
      p in P ==>
        0 <= p.opsLeft <= M.Length1) &&
    (forall p :: 
      p in P ==>
        y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)) &&
    (forall p :: 
      p in P ==>
        leftOvers[p.row] == p.opsLeft) &&
    (forall p :: 
      p in P ==>
        p.opsLeft == M.Length1 - p.curColumn) &&
    (sum(leftOvers[..]) > 0 ==>
      exists p :: 
        p in P &&
        p.opsLeft > 0)
  }
  // pure-end

  constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>, leftOvers: array<nat>)
    // pre-conditions-start
    requires forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1
    requires |processes| == leftOvers.Length
    requires |processes| == M_.Length0
    requires forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row
    requires forall p, q :: p in processes && q in processes ==> p != q
    requires forall p :: p in processes ==> 0 <= p.row < M_.Length0
    requires forall p :: p in processes ==> 0 == p.curColumn
    requires forall p :: p in processes ==> p.opsLeft == M_.Length1
    requires forall i :: 0 <= i < y_.Length ==> y_[i] == 0
    requires y_.Length == M_.Length0
    requires |x_| == M_.Length1
    requires M_.Length0 > 0
    requires |x_| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1
    ensures this.Valid(M_, x_, y_, processes, leftOvers)
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  method processNext(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers: array<nat>)
    // pre-conditions-start
    requires this.Valid(M, x, y, P, leftOvers)
    requires exists p :: p in P && p.opsLeft > 0
    requires sum(leftOvers[..]) > 0
    requires forall p, q :: p in P && q in P && p != q ==> p.row != q.row
    // pre-conditions-end
    // post-conditions-start
    modifies this, y, P, leftOvers
    ensures this.Valid(M, x, y, P, leftOvers)
    ensures sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1
    // post-conditions-end
  {
  // impl-start
    var p :| p in P && p.opsLeft > 0;
    y[p.row] := y[p.row] + M[p.row, p.curColumn] * x[p.curColumn];
    p.opsLeft := p.opsLeft - 1;
    p.curColumn := p.curColumn + 1;
    leftOvers[p.row] := leftOvers[p.row] - 1;
    // assert-start
    assert forall i :: 0 <= i < leftOvers.Length ==> i != p.row ==> leftOvers[i] == old(leftOvers[i]);
    // assert-end

    // assert-start
    assert leftOvers[p.row] + 1 == old(leftOvers[p.row]);
    // assert-end

    // assert-start
    assert forall p :: p in P ==> leftOvers[p.row] == p.opsLeft;
    // assert-end

    // assert-start
    sum_exept(old(leftOvers[..]), leftOvers[..], 1, p.row);
    // assert-end

  // impl-end
  }
}
