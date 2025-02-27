lemma peasantMultLemma(a: int, b: int)
  // pre-conditions-start
  requires b >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures b % 2 == 0 ==> a * b == 2 * a * b / 2
  ensures b % 2 == 1 ==> a * b == a + 2 * a * (b - 1) / 2
  // post-conditions-end
{
// impl-start
  if b % 2 == 0 && b > 0 {
    peasantMultLemma(a, b - 2);
  }
  if b % 2 == 1 && b > 1 {
    peasantMultLemma(a, b - 2);
  }
// impl-end
}

method peasantMult(a: int, b: int) returns (r: int)
  // pre-conditions-start
  requires b > 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == a * b
  // post-conditions-end
{
// impl-start
  r := 0;
  var aa := a;
  var bb := b;
  while bb > 0
    // invariants-start

    invariant 0 <= bb <= b
    invariant r + aa * bb == a * b
    decreases bb
    // invariants-end

  {
    if bb % 2 == 0 {
      aa := 2 * aa;
      bb := bb / 2;
    } else if bb % 2 == 1 {
      r := r + aa;
      aa := 2 * aa;
      bb := (bb - 1) / 2;
    }
  }
// impl-end
}

method euclidianDiv(a: int, b: int)
    returns (q: int, r: int)
  // pre-conditions-start
  requires a >= 0
  requires b > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a == b * q + r
  // post-conditions-end
{
// impl-start
  r := a;
  q := 0;
  while r - b >= 0
    // invariants-start

    invariant 0 <= r <= a
    invariant r == a - b * q
    decreases r - b
    // invariants-end

  {
    r := r - b;
    q := q + 1;
  }
// impl-end
}
