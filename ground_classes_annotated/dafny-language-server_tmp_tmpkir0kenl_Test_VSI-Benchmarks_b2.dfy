// dafny-language-server_tmp_tmpkir0kenl_Test_VSI-Benchmarks_b2.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[5];
  a[0] := -4;
  a[1] := -2;
  a[2] := -2;
  a[3] := 0;
  a[4] := 25;
  TestSearch(a, 4);
  TestSearch(a, -8);
  TestSearch(a, -2);
  TestSearch(a, 0);
  TestSearch(a, 23);
  TestSearch(a, 25);
  TestSearch(a, 27);
// impl-end
}

method TestSearch(a: array<int>, key: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var b := new Benchmark2;
  var r := b.BinarySearch(a, key);
  print "Looking for key=", key, ", result=", r, "\n";
// impl-end
}

class Benchmark2 {
  method BinarySearch(a: array<int>, key: int) returns (result: int)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    // pre-conditions-end
    // post-conditions-start
    ensures -1 <= result < a.Length
    ensures 0 <= result ==> a[result] == key
    ensures result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
    // post-conditions-end
  {
  // impl-start
    var low := 0;
    var high := a.Length;
    while low < high
      // invariants-start

      invariant 0 <= low <= high <= a.Length
      invariant forall i :: 0 <= i < low ==> a[i] < key
      invariant forall i :: high <= i < a.Length ==> key < a[i]
      // invariants-end

    {
      var mid := low + (high - low) / 2;
      var midVal := a[mid];
      if midVal < key {
        low := mid + 1;
      } else if key < midVal {
        high := mid;
      } else {
        result := mid;
        return;
      }
    }
    result := -1;
  // impl-end
  }
}
