method ComputeAvg(a: int, b: int) returns (avg: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures avg == (a + b) / 2
  // post-conditions-end
{
// impl-start
  avg := (a + b) / 2;
// impl-end
}
