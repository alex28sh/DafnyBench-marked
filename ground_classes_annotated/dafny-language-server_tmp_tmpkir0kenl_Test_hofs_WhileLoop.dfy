// dafny-language-server_tmp_tmpkir0kenl_Test_hofs_WhileLoop.dfy

method Nice(n: int) returns (k: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var f: int -> int := x => x;
  var i := new Ref<int>;
  i.val := 0;
  while i.val < n
    // invariants-start

    invariant forall u :: f.requires(u)
    invariant forall u :: f.reads(u) == {}
    invariant forall u :: f(u) == u + i.val
    // invariants-end

  {
    i.val := i.val + 1;
    f := x => f(x) + 1;
  }
  return f(0);
// impl-end
}

method OneShot(n: int) returns (k: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var f: int -> int := x => x;
  var i := 0;
  while i < n
    // invariants-start

    invariant forall u :: f.requires(u)
    invariant forall u :: f(u) == u + i
    // invariants-end

  {
    i := i + 1;
    f := x requires f.requires(x) reads f.reads(x) => f(x) + 1;
  }
  k := f(0);
// impl-end
}

method HeapQuant(n: int) returns (k: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var f: int -> int := x => x;
  var i := new Ref;
  ghost var r := 0;
  i.val := 0;
  while i.val < n
    // invariants-start

    invariant forall u :: f.requires(u)
    invariant forall u :: f.reads(u) == {}
    invariant r == i.val
    invariant forall u :: f(u) == u + r
    // invariants-end

  {
    i.val, r := i.val + 1, r + 1;
    f := x => f(x) + 1;
  }
  k := f(0);
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var k0 := Nice(22);
  var k1 := OneShot(22);
  var k2 := HeapQuant(22);
  print k0, " ", k1, " ", k2, "\n";
// impl-end
}

class Ref<A(0)> {
  var val: A
}
