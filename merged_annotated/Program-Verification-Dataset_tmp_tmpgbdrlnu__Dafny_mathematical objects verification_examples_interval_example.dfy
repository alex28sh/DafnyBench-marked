function contains(i: Interval, r: real): bool
{
  i.lo <= r <= i.hi
}
// pure-end

function empty(i: Interval): bool
{
  i.lo > i.hi
}
// pure-end

lemma empty_ok(i: Interval)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures empty(i) <==> !exists r :: contains(i, r)
  // post-conditions-end
{
// impl-start
  if empty(i) {
  } else {
    assert contains(i, i.lo);
  }
// impl-end
}

function min(r1: real, r2: real): real
{
  if r1 < r2 then
    r1
  else
    r2
}
// pure-end

function max(r1: real, r2: real): real
{
  if r1 > r2 then
    r1
  else
    r2
}
// pure-end

function intersect(i1: Interval, i2: Interval): Interval
{
  Interval(max(i1.lo, i2.lo), min(i1.hi, i2.hi))
}
// pure-end

lemma intersect_ok(i1: Interval, i2: Interval)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
  // post-conditions-end
{
// impl-start
// impl-end
}

function overlap(i1: Interval, i2: Interval): bool
{
  !empty(intersect(i1, i2))
}
// pure-end

lemma overlap_ok(i1: Interval, i2: Interval)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures overlap(i1, i2) <==> exists r :: contains(i1, r) && contains(i2, r)
  // post-conditions-end
{
// impl-start
  if overlap(i1, i2) {
    if i1.lo >= i2.lo {
      assert contains(i2, i1.lo);
    } else {
      assert contains(i1, i2.lo);
    }
  }
// impl-end
}

function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
{
  Interval(min(i1.lo, i2.lo), max(i1.hi, i2.hi))
}
// pure-end

lemma union_ok(i1: Interval, i2: Interval)
  // pre-conditions-start
  requires overlap(i1, i2)
  // pre-conditions-end
  // post-conditions-start
  ensures forall r :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  // pre-conditions-start
  requires overlap(i1, i2)
  // pre-conditions-end
  // post-conditions-start
  ensures contains(i1, r) && contains(i2, r)
  // post-conditions-end
{
// impl-start
  if i1.lo >= i2.lo {
    r := i1.lo;
  } else {
    r := i2.lo;
  }
// impl-end
}

datatype Interval = Interval(lo: real, hi: real)
