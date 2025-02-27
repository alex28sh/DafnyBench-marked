// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The RoundDown and RoundUp methods in this file are the ones in the Boogie
// implementation Source/AbsInt/IntervalDomain.cs.

class Rounding {
  var thresholds: array<int>

  function Valid(): bool
    reads this, this.thresholds
  {
    forall m,n :: 0 <= m < n < this.thresholds.Length ==> this.thresholds[m] <= this.thresholds[n]
  }

  method RoundDown(k: int) returns (r: int)
    requires this.Valid()
    ensures -1 <= r < this.thresholds.Length
    ensures forall m :: r < m < this.thresholds.Length ==> k < this.thresholds[m]
    ensures 0 <= r ==> this.thresholds[r] <= k
  {
    if (this.thresholds.Length == 0 || k < this.thresholds[0]) {
      return -1;
    }
    var i, j := 0, this.thresholds.Length - 1;
    while (i < j)
      invariant 0 <= i <= j < this.thresholds.Length
      invariant this.thresholds[i] <= k
      invariant forall m :: j < m < this.thresholds.Length ==> k < this.thresholds[m]
    {
      var mid := i + (j - i + 1) / 2;
      assert i < mid <= j;
      if (this.thresholds[mid] <= k) {
        i := mid;
      } else {
        j := mid - 1;
      }
    }
    return i;
  }

  method RoundUp(k: int) returns (r: int)
    requires this.Valid()
    ensures 0 <= r <= this.thresholds.Length
    ensures forall m :: 0 <= m < r ==> this.thresholds[m] < k
    ensures r < this.thresholds.Length ==> k <= this.thresholds[r]
  {
    if (this.thresholds.Length == 0 || this.thresholds[this.thresholds.Length-1] < k) {
      return this.thresholds.Length;
    }
    var i, j := 0, this.thresholds.Length - 1;
    while (i < j)
      invariant 0 <= i <= j < this.thresholds.Length
      invariant k <= this.thresholds[j]
      invariant forall m :: 0 <= m < i ==> this.thresholds[m] < k
    {
      var mid := i + (j - i) / 2;
      assert i <= mid < j;
      if (this.thresholds[mid] < k) {
        i := mid + 1;
      } else {
        j := mid;
      }
    }
    return i;
  }
}
