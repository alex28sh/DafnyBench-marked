function knows(a: int, b: int): bool
// pure-end

function isCelebrity(n: int, i: int): bool
  requires n >= 0 && 0 <= i < n
{
  forall j :: 
    0 <= j < n &&
    i != j ==>
      knows(j, i) &&
      !knows(i, j)
}
// pure-end

lemma knowerCannotBeCelebrity(n: int, i: int)
  // pre-conditions-start
  requires n >= 0 && 0 <= i < n
  // pre-conditions-end
  // post-conditions-start
  ensures (exists j :: 0 <= j < n && j != i && knows(i, j)) ==> !isCelebrity(n, i)
  // post-conditions-end
{
// impl-start
// impl-end
}

ghost method isCelebrityP(n: int, i: int) returns (r: bool)
  // pre-conditions-start
  requires n >= 0 && 0 <= i < n
  // pre-conditions-end
  // post-conditions-start
  ensures r <==> isCelebrity(n, i)
  // post-conditions-end
{
// impl-start
  var j := 0;
  r := true;
  while j < n
    invariant 0 <= j <= n
    invariant r ==> forall k :: 0 <= k < j && k != i ==> knows(k, i) && !knows(i, k)
    decreases n - j
  {
    if j != i {
      if !knows(j, i) || knows(i, j) {
        return false;
      }
    }
    j := j + 1;
  }
  return r;
// impl-end
}

ghost method findCelebrity(n: int) returns (r: int)
  // pre-conditions-start
  requires 2 <= n <= 100
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= r < n ==> isCelebrity(n, r)
  ensures r == -1 ==> forall i :: 0 <= i < n ==> !isCelebrity(n, i)
  // post-conditions-end
{
// impl-start
  var candidate := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall j :: 0 <= j < i && j != candidate ==> !isCelebrity(n, j)
    invariant 0 <= candidate < i
  {
    if knows(candidate, i) {
      candidate := i;
    }
    i := i + 1;
  }
  var isCelebrityC := isCelebrityP(n, candidate);
  if isCelebrityC {
    r := candidate;
  } else {
    r := -1;
  }
// impl-end
}
