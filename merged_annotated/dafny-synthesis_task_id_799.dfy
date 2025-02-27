method RotateLeftBits(n: bv32, d: int) returns (result: bv32)
  // pre-conditions-start
  requires 0 <= d < 32
  // pre-conditions-end
  // post-conditions-start
  ensures result == (n << d) | (n >> (32 - d))
  // post-conditions-end
{
// impl-start
  result := (n << d) | (n >> (32 - d));
// impl-end
}
