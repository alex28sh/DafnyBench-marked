method counting_bits(n: int) returns (result: array<int>)
  // pre-conditions-start
  requires 0 <= n <= 100000
  // pre-conditions-end
  // post-conditions-start
  ensures result.Length == n + 1
  ensures forall i :: 1 <= i < n + 1 ==> result[i] == result[i / 2] + i % 2
  // post-conditions-end
{
// impl-start
  result := new int[n + 1] (i => 0);
  var i := 1;
  while i < n + 1
    // invariants-start

    invariant 1 <= i <= n + 1
    invariant forall j :: 1 <= j < i ==> result[j] == result[j / 2] + j % 2
    // invariants-end

  {
    result[i] := result[i / 2] + i % 2;
    i := i + 1;
  }
// impl-end
}
