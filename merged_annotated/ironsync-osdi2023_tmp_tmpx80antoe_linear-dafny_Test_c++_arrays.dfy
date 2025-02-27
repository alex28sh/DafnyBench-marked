method returnANullArray() returns (a: array?<uint32>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == null
  // post-conditions-end
{
// impl-start
  a := null;
// impl-end
}

method returnANonNullArray() returns (a: array?<uint32>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a != null
  ensures a.Length == 5
  // post-conditions-end
{
// impl-start
  a := new uint32[5];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 4;
  a[4] := 5;
// impl-end
}

method LinearSearch(a: array<uint32>, len: uint32, key: uint32)
    returns (n: uint32)
  // pre-conditions-start
  requires a.Length == len as int
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= len
  ensures n == len || a[n] == key
  // post-conditions-end
{
// impl-start
  n := 0;
  while n < len
    // invariants-start

    invariant n <= len
    // invariants-end

  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
// impl-end
}

method PrintArray<A>(a: array?<A>, len: uint32)
  // pre-conditions-start
  requires a != null ==> len as int == a.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if a == null {
    print "It's null\n";
  } else {
    var i: uint32 := 0;
    while i < len
      // invariants-start

      // invariants-end
 {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new uint32[23];
  var i := 0;
  while i < 23
    // invariants-start

    // invariants-end
 {
    a[i] := i;
    i := i + 1;
  }
  PrintArray(a, 23);
  var n := LinearSearch(a, 23, 17);
  print n, "\n";
  var s: seq<uint32> := a[..];
  print s, "\n";
  s := a[2 .. 16];
  print s, "\n";
  s := a[20..];
  print s, "\n";
  s := a[..8];
  print s, "\n";
  a[0] := 42;
  print s, "\n";
  PrintArray<uint32>(null, 0);
  print "Null array:\n";
  var a1 := returnANullArray();
  PrintArray<uint32>(a1, 5);
  print "Non-Null array:\n";
  var a2 := returnANonNullArray();
  PrintArray<uint32>(a2, 5);
  print "Array in datatype:\n";
  var someAr := new uint32[3];
  someAr[0] := 1;
  someAr[1] := 3;
  someAr[2] := 9;
  var ad := AD(someAr);
  PrintArray<uint32>(ad.ar, 3);
// impl-end
}

newtype uint32 = i: int
  | 0 <= i < 4294967296

datatype ArrayDatatype = AD(ar: array<uint32>)
