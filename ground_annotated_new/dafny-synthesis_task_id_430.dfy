method ParabolaDirectrix(a: real, h: real, k: real)
    returns (directrix: real)
  // pre-conditions-start
  requires a != 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures directrix == k - 1.0 / (4.0 * a)
  // post-conditions-end
{
// impl-start
  directrix := k - 1.0 / (4.0 * a);
// impl-end
}
