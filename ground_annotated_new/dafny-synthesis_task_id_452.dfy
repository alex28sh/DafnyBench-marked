method CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
  // pre-conditions-start
  requires costPrice >= 0 && sellingPrice >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
  // post-conditions-end
{
// impl-start
  if costPrice > sellingPrice {
    loss := costPrice - sellingPrice;
  } else {
    loss := 0;
  }
// impl-end
}
