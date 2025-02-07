function eight(x: nat): nat
{
  9 * x + 5
}
// pure-end

function isOdd(x: nat): bool
{
  x % 2 == 1
}
// pure-end

function isEven(x: nat): bool
{
  x % 2 == 0
}
// pure-end

lemma eightL(x: nat)
  // pre-conditions-start
  requires isOdd(x)
  // pre-conditions-end
  // post-conditions-start
  ensures isEven(eight(x))
  // post-conditions-end
{
// impl-start
// impl-end
}

function nineteenf(x: nat): nat
{
  7 * x + 4
}
// pure-end

function nineteens(x: nat): nat
{
  3 * x + 11
}
// pure-end

lemma nineteenlemma(x: nat)
  // pre-conditions-start
  requires isEven(nineteenf(x))
  // pre-conditions-end
  // post-conditions-start
  ensures isOdd(nineteens(x))
  // post-conditions-end
{
// impl-start
// impl-end
}

function relationDomain<T>(s: set<(T, T)>): set<T>
{
  set z | z in s :: z.1
}
// pure-end

function reflexive<T>(R: set<(T, T)>, S: set<T>): bool
  requires relationOnASet(R, S)
{
  forall s :: 
    s in S ==>
      (s, s) in R
}
// pure-end

function symmetric<T>(R: set<(T, T)>, S: set<T>): bool
  requires relationOnASet(R, S)
{
  forall x: T, y: T :: 
    x in S &&
    y in S &&
    (x, y) in R ==>
      (y, x) in R
}
// pure-end

function transitive<T>(R: set<(T, T)>, S: set<T>): bool
  requires relationOnASet(R, S)
{
  forall a, b, c :: 
    a in S &&
    b in S &&
    c in S &&
    (a, b) in R &&
    (b, c) in R ==>
      (a, c) in R
}
// pure-end

function equivalenceRelation<T>(R: set<(T, T)>, S: set<T>): bool
  requires relationOnASet(R, S)
{
  reflexive(R, S) &&
  symmetric(R, S) &&
  transitive(R, S)
}
// pure-end

function relationOnASet<T>(R: set<(T, T)>, S: set<T>): bool
{
  forall ts :: 
    ts in R ==>
      ts.0 in S &&
      ts.1 in S
}
// pure-end

lemma reflexiveUnion<T>(R_1: set<(T, T)>, S_1: set<T>, R_2: set<(T, T)>, S_2: set<T>)
  // pre-conditions-start
  requires |R_1| > 0
  requires |R_2| > 0
  requires |S_1| > 0
  requires |S_2| > 0
  requires relationOnASet(R_1, S_1)
  requires relationOnASet(R_2, S_2)
  requires reflexive(R_1, S_1)
  requires reflexive(R_2, S_2)
  // pre-conditions-end
  // post-conditions-start
  ensures reflexive(R_1 + R_2, S_1 + S_2)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma symmetricUnion<T>(R_1: set<(T, T)>, S_1: set<T>, R_2: set<(T, T)>, S_2: set<T>)
  // pre-conditions-start
  requires |R_1| > 0
  requires |R_2| > 0
  requires |S_1| > 0
  requires |S_2| > 0
  requires relationOnASet(R_1, S_1)
  requires relationOnASet(R_2, S_2)
  requires symmetric(R_1, S_1)
  requires symmetric(R_2, S_2)
  // pre-conditions-end
  // post-conditions-start
  ensures symmetric(R_1 + R_2, S_1 + S_2)
  // post-conditions-end
{
// impl-start
  forall x, y | x in S_1 + S_2 && y in S_1 + S_2 && (x, y) in R_1 + R_2
    ensures (y, x) in R_1 + R_2
  {
    if x in S_1 && y in S_1 && (x, y) in R_1 {
      assert (y, x) in R_1 + R_2;
    } else if x in S_2 && y in S_2 && (x, y) in R_2 {
      assert (y, x) in R_1 + R_2;
    }
  }
// impl-end
}

lemma transitiveUnion<T>(R_1: set<(T, T)>, S_1: set<T>, R_2: set<(T, T)>, S_2: set<T>)
  // pre-conditions-start
  requires |R_1| > 0
  requires |R_2| > 0
  requires |S_1| > 0
  requires |S_2| > 0
  requires relationOnASet(R_1, S_1)
  requires relationOnASet(R_2, S_2)
  requires transitive(R_1, S_1)
  requires transitive(R_2, S_2)
  // pre-conditions-end
  // post-conditions-start
  ensures transitive(R_1 + R_2, S_1 + S_2)
  // post-conditions-end
{
// impl-start
  assert R_1 <= R_1 + R_2;
  assert R_2 <= R_1 + R_2;
  assume forall a :: a in S_1 + S_2 ==> a !in S_1 || a !in S_2;
  forall a, b, c | a in S_1 + S_2 && b in S_1 + S_2 && c in S_1 + S_2 && (a, b) in R_1 + R_2 && (b, c) in R_1 + R_2
    ensures (a, c) in R_1 + R_2
  {
    assert a in S_1 ==> b !in S_2;
    if a in S_1 && b in S_1 && c in S_1 && (a, b) in R_1 && (b, c) in R_1 {
      assert (a, c) in R_1;
      assert (a, c) in R_1 + R_2;
    } else if a in S_2 && b in S_2 && c in S_2 && (a, b) in R_2 && (b, c) in R_2 {
      assert (a, c) in R_2;
      assert (a, c) in R_1 + R_2;
    }
  }
// impl-end
}

lemma transitiveUnionContra<T>()
    returns (R1: set<(T, T)>, S1: set<T>, R2: set<(T, T)>, S2: set<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures relationOnASet(R1, S1)
  ensures relationOnASet(R2, S2)
  ensures transitive(R1, S1)
  ensures transitive(R2, S2)
  ensures !transitive(R1 + R2, S1 + S2)
  // post-conditions-end
{
// impl-start
  var a: T :| assume true;
  var b: T :| assume a != b;
  var c: T :| assume a != c && b != c;
  S1 := {a, b};
  S2 := {b, c};
  R1 := {(a, b)};
  R2 := {(b, c)};
// impl-end
}

lemma notTrueAlways<T>()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !forall S1: set<T>, S2: set<T>, R1: set<(T, T)>, R2: set<(T, T)> :: relationOnASet(R1, S1) && relationOnASet(R2, S2) && transitive(R1, S1) && transitive(R2, S2) ==> transitive(R1 + R2, S1 + S2)
  // post-conditions-end
{
// impl-start
  var a, b, c, d := transitiveUnionContra<T>();
// impl-end
}

method test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var x := 7;
  var four := 4;
  var sample := {1, 2, 3, 4, 5, 6};
  var test := set x, y | x in sample && y in sample :: (x, y);
  var modulos := set x, y | x in sample && y in sample && x % y == 0 :: (x, y);
  // assert-start
  assert reflexive(test, sample);
  // assert-end

  // assert-start
  assert symmetric(test, sample);
  // assert-end

  // assert-start
  assert transitive(test, sample);
  // assert-end

  // assert-start
  assert equivalenceRelation(test, sample);
  // assert-end

  var hmm := (1, 2, 3);
  // assert-start
  assert hmm.2 == 3;
  // assert-end

  // assert-start
  assert (1, 2) in test;
  // assert-end

  ghost var y: nat :| isEven(nineteenf(y));
  // assert-start
  assert isOdd(nineteens(y));
  // assert-end

// impl-end
}
