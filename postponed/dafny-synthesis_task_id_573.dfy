method UniqueProduct(arr: array<int>) returns (product: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures product == SetProduct(set i | 0 <= i < arr.Length :: arr[i])
  // post-conditions-end
{
// impl-start
  var p := 1;
  var seen: set<int> := {};
  for i := 0 to arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant seen == set k | 0 <= k < i :: arr[k]
    invariant p == SetProduct(set k | 0 <= k < i :: arr[k])
    // invariants-end

  {
    if !(arr[i] in seen) {
      seen := seen + {arr[i]};
      p := p * arr[i];
      // assert-start
      SetProductLemma(seen, arr[i]);
      // assert-end

    }
  }
  product := p;
// impl-end
}

function SetProduct(s: set<int>): int
{
  if s == {} then
    1
  else
    var x :| x in s; x * SetProduct(s - {x})
}
// pure-end

lemma SetProductLemma(s: set<int>, x: int)
  // pre-conditions-start
  requires x in s
  // pre-conditions-end
  // post-conditions-start
  ensures SetProduct(s - {x}) * x == SetProduct(s)
  // post-conditions-end
{
// impl-start
  if s != {} {
    var y :| y in s && y * SetProduct(s - {y}) == SetProduct(s);
    if y == x {
    } else {
      calc {
        SetProduct(s);
        y * SetProduct(s - {y});
        {
          SetProductLemma(s - {y}, x);
        }
        y * x * SetProduct(s - {y} - {x});
        {
          assert s - {x} - {y} == s - {y} - {x};
        }
        y * x * SetProduct(s - {x} - {y});
        x * y * SetProduct(s - {x} - {y});
        {
          SetProductLemma(s - {x}, y);
        }
        x * SetProduct(s - {x});
      }
    }
  }
// impl-end
}
