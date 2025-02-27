// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week8_CheckSumCalculator.dfy

ghost function Hash(s: string): int
{
  SumChars(s) % 137
}
// pure-end

ghost function SumChars(s: string): int
{
  if |s| == 0 then
    0
  else
    s[|s| - 1] as int + SumChars(s[..|s| - 1])
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var newSeq := ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];
  var newSeqTwo := ['h', 'g', 'f', 'e', 'd', 'c', 'b', 'a'];
  var newSet: set<int>;
  newSet := {1, 2, 3, 4, 5};
  var newSetTwo := {6, 7, 8, 9, 10};
  print "element is newset ", newSet, "\n";
  var newArray := new int[99];
  newArray[0] := 99;
  newArray[1] := 2;
  print "element is ?  ", |[newArray]|, "\n";
  var tmpSet := {'a', 'c'};
  var tmpFresh := {'c'};
  print "tmp is ", tmpSet - tmpFresh;
  var newMap := map[];
  newMap := newMap[1 := 2];
  var nnewMap := map[3 := 444];
  print "keys is ", newMap.Keys, newMap.Values;
  print "value is", nnewMap.Keys, nnewMap.Values;
// impl-end
}

class CheckSumCalculator {
  var data: string
  var cs: int

  ghost predicate Valid()
    reads this
  {
    this.cs == Hash(this.data)
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.Valid() && this.data == ""
    // post-conditions-end
  {
  // impl-start
    this.data, this.cs := "", 0;
  // impl-end
  }

  method Append(d: string)
    // pre-conditions-start
    requires this.Valid()
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid() && this.data == old(this.data) + d
    // post-conditions-end
  {
  // impl-start
    var i := 0;
    while i != |d|
      // invariants-start

      invariant 0 <= i <= |d|
      invariant this.Valid()
      invariant this.data == old(this.data) + d[..i]
      // invariants-end

    {
      this.cs := (this.cs + d[i] as int) % 137;
      this.data := this.data + [d[i]];
      i := i + 1;
    }
  // impl-end
  }

  function GetData(): string
    requires this.Valid()
    reads this
    ensures Hash(this.GetData()) == this.Checksum()
  {
    this.data
  }
  // pure-end

  function Checksum(): int
    requires this.Valid()
    reads this
    ensures this.Checksum() == Hash(this.data)
  {
    this.cs
  }
  // pure-end
}
