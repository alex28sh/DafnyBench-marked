method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  // pre-conditions-start
  requires costPrice >= 0 && sellingPrice >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> costPrice == sellingPrice
  // post-conditions-end
{
// impl-start
  result := costPrice == sellingPrice;
// impl-end
}
