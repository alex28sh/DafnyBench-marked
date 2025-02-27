
function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n - 1)
}
// pure-end

lemma sum_plus(s: seq<int>, i: nat)
  // pre-conditions-start
  requires i < |s|
  // pre-conditions-end
  // post-conditions-start
  ensures sum(s, i) + s[i] == sum(s, i + 1)
  // post-conditions-end
{
// impl-start
// impl-end
}

method BelowZero(ops: seq<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
  // post-conditions-end
{
// impl-start
  result := false;
  var t := 0;
  for i := 0 to |ops|
    // invariants-start

    invariant t == sum(ops, i)
    invariant forall n: nat :: n <= i ==> sum(ops, n) >= 0
    // invariants-end

  {
    t := t + ops[i];
    // assert-start
    sum_plus(ops, i);
    // assert-end

    if t < 0 {
      result := true;
      return;
    }
  }
// impl-end
}
