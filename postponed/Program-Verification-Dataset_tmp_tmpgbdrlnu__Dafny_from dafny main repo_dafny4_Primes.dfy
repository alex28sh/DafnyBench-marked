function IsPrime(n: int): bool
{
  2 <= n &&
  forall m :: 
    2 <= m < n ==>
      n % m != 0
}
// pure-end

lemma AlwaysMorePrimes(k: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists p :: k <= p && IsPrime(p)
  // post-conditions-end
{
// impl-start
  var j, s := 0, {};
  while true
    invariant AllPrimes(s, j)
    decreases k - j
  {
    var p := GetLargerPrime(s, j);
    if k <= p {
      return;
    }
    j, s := p, set x | 2 <= x <= p && IsPrime(x);
  }
// impl-end
}

lemma NoFiniteSetContainsAllPrimes(s: set<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures exists p :: IsPrime(p) && p !in s
  // post-conditions-end
{
// impl-start
  AlwaysMorePrimes(if s == {} then 0 else PickLargest(s) + 1);
// impl-end
}

function AllPrimes(s: set<int>, bound: int): bool
{
  (forall x :: 
    x in s ==>
      IsPrime(x)) &&
  forall p :: 
    IsPrime(p) &&
    p <= bound ==>
      p in s
}
// pure-end

lemma GetLargerPrime(s: set<int>, bound: int) returns (p: int)
  // pre-conditions-start
  requires AllPrimes(s, bound)
  // pre-conditions-end
  // post-conditions-start
  ensures bound < p && IsPrime(p)
  // post-conditions-end
{
// impl-start
  var q := product(s);
  if exists p :: bound < p <= q && IsPrime(p) {
    p :| bound < p <= q && IsPrime(p);
  } else {
    ProductPlusOneIsPrime(s, q);
    p := q + 1;
    if p <= bound {
      assert p in s;
      product_property(s);
      assert false;
    }
  }
// impl-end
}

function product(s: set<int>): int
{
  if s == {} then
    1
  else
    var a := PickLargest(s); a * product(s - {a})
}
// pure-end

lemma product_property(s: set<int>)
  // pre-conditions-start
  requires forall x :: x in s ==> 1 <= x
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= product(s) && forall x :: x in s ==> x <= product(s)
  // post-conditions-end
{
// impl-start
  if s != {} {
    var a := PickLargest(s);
    var s' := s - {a};
    assert s == s' + {a};
    product_property(s');
    MulPos(a, product(s'));
  }
// impl-end
}

lemma ProductPlusOneIsPrime(s: set<int>, q: int)
  // pre-conditions-start
  requires AllPrimes(s, q) && q == product(s)
  // pre-conditions-end
  // post-conditions-start
  ensures IsPrime(q + 1)
  // post-conditions-end
{
// impl-start
  var p := q + 1;
  calc {
    true;
    {
      product_property(s);
    }
    2 <= p;
  }
  forall m | 2 <= m <= q && IsPrime(m)
    ensures p % m != 0
  {
    assert m in s;
    RemoveFactor(m, s);
    var l := product(s - {m});
    assert m * l == q;
    MulDivMod(m, l, q, 1);
  }
  assert IsPrime_Alt(q + 1);
  AltPrimeDefinition(q + 1);
// impl-end
}

lemma RemoveFactor(x: int, s: set<int>)
  // pre-conditions-start
  requires x in s
  // pre-conditions-end
  // post-conditions-start
  ensures product(s) == x * product(s - {x})
  // post-conditions-end
{
// impl-start
  var y := PickLargest(s);
  if x != y {
    calc {
      product(s);
      y * product(s - {y});
      {
        RemoveFactor(x, s - {y});
      }
      y * x * product(s - {y} - {x});
      x * y * product(s - {y} - {x});
      {
        assert s - {y} - {x} == s - {x} - {y};
      }
      x * y * product(s - {x} - {y});
      {
        assert y in s - {x};
      }
      {
        assert y == PickLargest(s - {x});
      }
      x * product(s - {x});
    }
  }
// impl-end
}

function IsPrime_Alt(n: int): bool
{
  2 <= n &&
  forall m :: 
    2 <= m < n &&
    IsPrime(m) ==>
      n % m != 0
}
// pure-end

lemma AltPrimeDefinition(n: int)
  // pre-conditions-start
  requires IsPrime_Alt(n)
  // pre-conditions-end
  // post-conditions-start
  ensures IsPrime(n)
  // post-conditions-end
{
// impl-start
  forall m | 2 <= m < n
    ensures n % m != 0
  {
    if !IsPrime(m) {
      var a, b := Composite(m);
      if n % m == 0 {
        var k := n / m;
        calc {
          true;
          k == n / m;
          m * k == n;
          a * b * k == n;
        ==>
          {
            MulDivMod(a, b * k, n, 0);
          }
          n % a == 0;
        ==>
          !(2 <= a < n && IsPrime(a));
          {
            assert 2 <= a < m < n;
          }
          !IsPrime(a);
          false;
        }
      }
    }
  }
// impl-end
}

lemma Composite(c: int) returns (a: int, b: int)
  // pre-conditions-start
  requires 2 <= c && !IsPrime(c)
  // pre-conditions-end
  // post-conditions-start
  ensures 2 <= a < c && 2 <= b && a * b == c
  ensures IsPrime(a)
  // post-conditions-end
{
// impl-start
  calc {
    true;
    !IsPrime(c);
    !(2 <= c && forall m :: 2 <= m < c ==> c % m != 0);
    exists m :: 
      2 <= m < c &&
      c % m == 0;
  }
  a :| 2 <= a < c && c % a == 0;
  b := c / a;
  assert 2 <= a < c && 2 <= b && a * b == c;
  if !IsPrime(a) {
    var x, y := Composite(a);
    a, b := x, y * b;
  }
// impl-end
}

function PickLargest(s: set<int>): int
  requires s != {}
{
  LargestElementExists(s);
  var x :| x in s && forall y :: y in s ==> y <= x;
  x
}
// pure-end

lemma LargestElementExists(s: set<int>)
  // pre-conditions-start
  requires s != {}
  // pre-conditions-end
  // post-conditions-start
  ensures exists x :: x in s && forall y :: y in s ==> y <= x
  // post-conditions-end
{
// impl-start
  var s' := s;
  while true
    invariant s' != {} && s' <= s
    invariant forall x, y :: x in s' && y in s && y !in s' ==> y <= x
    decreases s'
  {
    var x :| x in s';
    if forall y :: y in s' ==> y <= x {
      return;
    } else {
      var y :| y in s' && x < y;
      s' := set z | z in s && x < z;
      assert y in s';
    }
  }
// impl-end
}

lemma MulPos(a: int, b: int)
  // pre-conditions-start
  requires 1 <= a && 1 <= b
  // pre-conditions-end
  // post-conditions-start
  ensures a <= a * b
  // post-conditions-end
{
// impl-start
  if b == 1 {
    assert a * b == a;
  } else {
    assert a * b == a * (b - 1) + a;
    MulPos(a, b - 1);
  }
// impl-end
}

lemma MulDivMod(a: nat, b: nat, c: nat, j: nat)
  // pre-conditions-start
  requires a * b == c && j < a
  // pre-conditions-end
  // post-conditions-start
  ensures (c + j) % a == j
  // post-conditions-end
