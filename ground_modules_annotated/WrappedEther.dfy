// WrappedEther.dfy


module Int {
  const TWO_7: int := 128
  const TWO_8: int := 256
  const TWO_15: int := 32768
  const TWO_16: int := 65536
  const TWO_24: int := 16777216
  const TWO_31: int := 2147483648
  const TWO_32: int := 4294967296
  const TWO_40: int := 1099511627776
  const TWO_48: int := 281474976710656
  const TWO_56: int := 72057594037927936
  const TWO_63: int := 9223372036854775808
  const TWO_64: int := 18446744073709551616
  const TWO_127: int := 170141183460469231731687303715884105728
  const TWO_128: int := 340282366920938463463374607431768211456
  const TWO_160: int := 1461501637330902918203684832716283019655932542976
  const TWO_255: int := 57896044618658097711785492504343953926634992332820282019728792003956564819968
  const TWO_256: int := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const MIN_I8: int := -TWO_7
  const MAX_I8: int := TWO_7 - 1
  const MIN_I16: int := -TWO_15
  const MAX_I16: int := TWO_15 - 1
  const MIN_I32: int := -TWO_31
  const MAX_I32: int := TWO_31 - 1
  const MIN_I64: int := -TWO_63
  const MAX_I64: int := TWO_63 - 1
  const MIN_I128: int := -TWO_127
  const MAX_I128: int := TWO_127 - 1
  const MIN_I256: int := -TWO_255
  const MAX_I256: int := TWO_255 - 1
  const MAX_U8: int := TWO_8 - 1
  const MAX_U16: int := TWO_16 - 1
  const MAX_U24: int := TWO_24 - 1
  const MAX_U32: int := TWO_32 - 1
  const MAX_U40: int := TWO_40 - 1
  const MAX_U48: int := TWO_48 - 1
  const MAX_U56: int := TWO_56 - 1
  const MAX_U64: int := TWO_64 - 1
  const MAX_U128: int := TWO_128 - 1
  const MAX_U160: int := TWO_160 - 1
  const MAX_U256: int := TWO_256 - 1

  function Max(i1: int, i2: int): int
  {
    if i1 >= i2 then
      i1
    else
      i2
  }
  // pure-end

  function Min(i1: int, i2: int): int
  {
    if i1 < i2 then
      i1
    else
      i2
  }
  // pure-end

  function RoundUp(i: int, r: nat): int
    requires r > 0
  {
    if i % r == 0 then
      i
    else
      i / r * r + r
  }
  // pure-end

  function MaxUnsignedN(n: nat): (r: nat)
    requires 1 <= n <= 32
  {
    match n
    case 1 =>
      MAX_U8
    case 2 =>
      MAX_U16
    case 3 =>
      MAX_U24
    case 4 =>
      MAX_U32
    case 5 =>
      MAX_U40
    case 6 =>
      MAX_U48
    case 7 =>
      MAX_U56
    case 8 =>
      MAX_U64
    case 16 =>
      MAX_U128
    case 20 =>
      MAX_U160
    case 32 =>
      MAX_U256
    case _ /* _v0 */ =>
      Pow(2, n) - 1
  }
  // pure-end

  function Pow(n: nat, k: nat): (r: nat)
    ensures n > 0 ==> r > 0
  {
    if k == 0 then
      1
    else if k == 1 then
      n
    else
      var p := k / 2; var np := Pow(n, p); if p * 2 == k then np * np else np * np * n
  }
  // pure-end

  lemma lemma_pow2(k: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures Pow(2, k) > 0
    // post-conditions-end
  {
  // impl-start
    if k == 0 {
      assert Pow(2, k) == 1;
    } else if k == 1 {
      assert Pow(2, k) == 2;
    } else {
      lemma_pow2(k / 2);
    }
  // impl-end
  }

  function Div(lhs: int, rhs: int): int
    requires rhs != 0
  {
    if lhs >= 0 then
      lhs / rhs
    else
      -(-lhs / rhs)
  }
  // pure-end

  function Rem(lhs: int, rhs: int): int
    requires rhs != 0
  {
    if lhs >= 0 then
      lhs % rhs
    else
      var d := -(-lhs / rhs); lhs - d * rhs
  }
  // pure-end

  newtype {:nativeType "sbyte"} i8 = i: int
    | MIN_I8 <= i <= MAX_I8

  newtype {:nativeType "short"} i16 = i: int
    | MIN_I16 <= i <= MAX_I16

  newtype {:nativeType "int"} i32 = i: int
    | MIN_I32 <= i <= MAX_I32

  newtype {:nativeType "long"} i64 = i: int
    | MIN_I64 <= i <= MAX_I64

  newtype i128 = i: int
    | MIN_I128 <= i <= MAX_I128

  newtype i256 = i: int
    | MIN_I256 <= i <= MAX_I256

  newtype {:nativeType "byte"} u8 = i: int
    | 0 <= i <= MAX_U8

  newtype {:nativeType "ushort"} u16 = i: int
    | 0 <= i <= MAX_U16

  newtype {:nativeType "uint"} u24 = i: int
    | 0 <= i <= MAX_U24

  newtype {:nativeType "uint"} u32 = i: int
    | 0 <= i <= MAX_U32

  newtype {:nativeType "ulong"} u40 = i: int
    | 0 <= i <= MAX_U40

  newtype {:nativeType "ulong"} u48 = i: int
    | 0 <= i <= MAX_U48

  newtype {:nativeType "ulong"} u56 = i: int
    | 0 <= i <= MAX_U56

  newtype {:nativeType "ulong"} u64 = i: int
    | 0 <= i <= MAX_U64

  newtype u128 = i: int
    | 0 <= i <= MAX_U128

  newtype u160 = i: int
    | 0 <= i <= MAX_U160

  newtype u256 = i: int
    | 0 <= i <= MAX_U256
}

module U8 {
  function Log2(v: u8): (r: nat)
    ensures r < 8
  {
    if v <= 15 then
      if v <= 3 then
        if v <= 1 then
          0
        else
          1
      else if v <= 7 then
        2
      else
        3
    else if v <= 63 then
      if v <= 31 then
        4
      else
        5
    else if v <= 127 then
      6
    else
      7
  }
  // pure-end

  import opened Int
}

module U16 {
  function NthUint8(v: u16, k: nat): u8
    requires k < 2
  {
    if k == 0 then
      (v / TWO_8 as u16) as u8
    else
      (v % TWO_8 as u16) as u8
  }
  // pure-end

  function Log2(v: u16): (r: nat)
    ensures r < 16
  {
    var low := (v % TWO_8 as u16) as u8;
    var high := (v / TWO_8 as u16) as u8;
    if high != 0 then
      U8.Log2(high) + 8
    else
      U8.Log2(low)
  }
  // pure-end

  function Log256(v: u16): (r: nat)
    ensures r <= 1
  {
    var low := (v % TWO_8 as u16) as u8;
    var high := (v / TWO_8 as u16) as u8;
    if high != 0 then
      1
    else
      0
  }
  // pure-end

  function ToBytes(v: u16): (r: seq<u8>)
    ensures |r| == 2
  {
    var low := (v % TWO_8 as u16) as u8;
    var high := (v / TWO_8 as u16) as u8;
    [high, low]
  }
  // pure-end

  function Read(bytes: seq<u8>, address: nat): u16
    requires address + 1 < |bytes|
  {
    var b1 := bytes[address] as u16;
    var b2 := bytes[address + 1] as u16;
    b1 * TWO_8 as u16 + b2
  }
  // pure-end

  import opened Int

  import U8
}

module U32 {
  function NthUint16(v: u32, k: nat): u16
    requires k < 2
  {
    if k == 0 then
      (v / TWO_16 as u32) as u16
    else
      (v % TWO_16 as u32) as u16
  }
  // pure-end

  function Log2(v: u32): (r: nat)
    ensures r < 32
  {
    var low := (v % TWO_16 as u32) as u16;
    var high := (v / TWO_16 as u32) as u16;
    if high != 0 then
      U16.Log2(high) + 16
    else
      U16.Log2(low)
  }
  // pure-end

  function Log256(v: u32): (r: nat)
    ensures r <= 3
  {
    var low := (v % TWO_16 as u32) as u16;
    var high := (v / TWO_16 as u32) as u16;
    if high != 0 then
      U16.Log256(high) + 2
    else
      U16.Log256(low)
  }
  // pure-end

  function ToBytes(v: u32): (r: seq<u8>)
    ensures |r| == 4
  {
    var low := (v % TWO_16 as u32) as u16;
    var high := (v / TWO_16 as u32) as u16;
    U16.ToBytes(high) + U16.ToBytes(low)
  }
  // pure-end

  function Read(bytes: seq<u8>, address: nat): u32
    requires address + 3 < |bytes|
  {
    var b1 := U16.Read(bytes, address) as u32;
    var b2 := U16.Read(bytes, address + 2) as u32;
    b1 * TWO_16 as u32 + b2
  }
  // pure-end

  import U16

  import opened Int
}

module U64 {
  function NthUint32(v: u64, k: nat): u32
    requires k < 2
  {
    if k == 0 then
      (v / TWO_32 as u64) as u32
    else
      (v % TWO_32 as u64) as u32
  }
  // pure-end

  function Log2(v: u64): (r: nat)
    ensures r < 64
  {
    var low := (v % TWO_32 as u64) as u32;
    var high := (v / TWO_32 as u64) as u32;
    if high != 0 then
      U32.Log2(high) + 32
    else
      U32.Log2(low)
  }
  // pure-end

  function Log256(v: u64): (r: nat)
    ensures r <= 7
  {
    var low := (v % TWO_32 as u64) as u32;
    var high := (v / TWO_32 as u64) as u32;
    if high != 0 then
      U32.Log256(high) + 4
    else
      U32.Log256(low)
  }
  // pure-end

  function ToBytes(v: u64): (r: seq<u8>)
    ensures |r| == 8
  {
    var low := (v % TWO_32 as u64) as u32;
    var high := (v / TWO_32 as u64) as u32;
    U32.ToBytes(high) + U32.ToBytes(low)
  }
  // pure-end

  function Read(bytes: seq<u8>, address: nat): u64
    requires address + 7 < |bytes|
  {
    var b1 := U32.Read(bytes, address) as u64;
    var b2 := U32.Read(bytes, address + 4) as u64;
    b1 * TWO_32 as u64 + b2
  }
  // pure-end

  import U32

  import opened Int
}

module U128 {
  function NthUint64(v: u128, k: nat): u64
    requires k < 2
  {
    if k == 0 then
      (v / TWO_64 as u128) as u64
    else
      (v % TWO_64 as u128) as u64
  }
  // pure-end

  function Log2(v: u128): (r: nat)
    ensures r < 128
  {
    var low := (v % TWO_64 as u128) as u64;
    var high := (v / TWO_64 as u128) as u64;
    if high != 0 then
      U64.Log2(high) + 64
    else
      U64.Log2(low)
  }
  // pure-end

  function Log256(v: u128): (r: nat)
    ensures r <= 15
  {
    var low := (v % TWO_64 as u128) as u64;
    var high := (v / TWO_64 as u128) as u64;
    if high != 0 then
      U64.Log256(high) + 8
    else
      U64.Log256(low)
  }
  // pure-end

  function ToBytes(v: u128): (r: seq<u8>)
    ensures |r| == 16
  {
    var low := (v % TWO_64 as u128) as u64;
    var high := (v / TWO_64 as u128) as u64;
    U64.ToBytes(high) + U64.ToBytes(low)
  }
  // pure-end

  function Read(bytes: seq<u8>, address: nat): u128
    requires address + 15 < |bytes|
  {
    var b1 := U64.Read(bytes, address) as u128;
    var b2 := U64.Read(bytes, address + 8) as u128;
    b1 * TWO_64 as u128 + b2
  }
  // pure-end

  import U64

  import opened Int
}

module U256 {
  lemma {:axiom} as_bv256_as_u256(v: bv256)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures v as nat < TWO_256
    // post-conditions-end

  function Shl(lhs: u256, rhs: u256): u256
  {
    var lbv := lhs as bv256;
    var res := if rhs < 256 then lbv << rhs else 0;
    res as u256
  }
  // pure-end

  function Shr(lhs: u256, rhs: u256): u256
  {
    var lbv := lhs as bv256;
    var res := if rhs < 256 then lbv >> rhs else 0;
    res as u256
  }
  // pure-end

  function Log2(v: u256): (r: nat)
    ensures r < 256
  {
    var low := (v % TWO_128 as u256) as u128;
    var high := (v / TWO_128 as u256) as u128;
    if high != 0 then
      U128.Log2(high) + 128
    else
      U128.Log2(low)
  }
  // pure-end

  function Log256(v: u256): (r: nat)
    ensures r <= 31
  {
    var low := (v % TWO_128 as u256) as u128;
    var high := (v / TWO_128 as u256) as u128;
    if high != 0 then
      U128.Log256(high) + 16
    else
      U128.Log256(low)
  }
  // pure-end

  function NthUint128(v: u256, k: nat): u128
    requires k < 2
  {
    if k == 0 then
      (v / TWO_128 as u256) as u128
    else
      (v % TWO_128 as u256) as u128
  }
  // pure-end

  function NthUint8(v: u256, k: nat): u8
    requires k < 32
  {
    var w128 := NthUint128(v, k / 16);
    var w64 := U128.NthUint64(w128, k % 16 / 8);
    var w32 := U64.NthUint32(w64, k % 8 / 4);
    var w16 := U32.NthUint16(w32, k % 4 / 2);
    U16.NthUint8(w16, k % 2)
  }
  // pure-end

  function Read(bytes: seq<u8>, address: nat): u256
    requires address + 31 < |bytes|
  {
    var b1 := U128.Read(bytes, address) as u256;
    var b2 := U128.Read(bytes, address + 16) as u256;
    b1 * TWO_128 as u256 + b2
  }
  // pure-end

  function ToBytes(v: u256): (r: seq<u8>)
    ensures |r| == 32
  {
    var low := (v % TWO_128 as u256) as u128;
    var high := (v / TWO_128 as u256) as u128;
    U128.ToBytes(high) + U128.ToBytes(low)
  }
  // pure-end

  function SignExtend(v: u256, k: nat): u256
  {
    if k >= 31 then
      v
    else
      var ith := 31 - k; var byte := NthUint8(v, ith); var signbit := byte as bv8 & 128 == 128; var signs := if signbit then seq(31 - k, i => 255) else seq(31 - k, i => 0); var bytes := ToBytes(v)[ith..]; assert |signs + bytes| == 32; Read(signs + bytes, 0)
  }
  // pure-end

  import opened Int

  import U8

  import U16

  import U32

  import U64

  import U128
}

module I256 {
  function Div(lhs: i256, rhs: i256): i256
    requires rhs != 0
    requires rhs != -1 || lhs != -TWO_255 as i256
  {
    Int.Div(lhs as int, rhs as int) as i256
  }
  // pure-end

  function Rem(lhs: i256, rhs: i256): i256
    requires rhs != 0
  {
    Int.Rem(lhs as int, rhs as int) as i256
  }
  // pure-end

  lemma ShiftYieldsNonZero(x: u256)
    // pre-conditions-start
    requires 0 < x < 256
    // pre-conditions-end
    // post-conditions-start
    ensures U256.Shl(1, x) > 0
    // post-conditions-end
  {
  // impl-start
  // impl-end
  }

  function Sar(lhs: i256, rhs: u256): i256
  {
    if rhs == 0 then
      lhs
    else if rhs < 256 then
      assert 0 < rhs < 256;
      var r := U256.Shl(1, rhs);
      ShiftYieldsNonZero(rhs);
      (lhs as int / r as int) as i256
    else if lhs < 0 then
      -1
    else
      0
  }
  // pure-end

  import U256

  import Word

  import opened Int
}

module Word {
  function asI256(w: u256): i256
  {
    if w > MAX_I256 as u256 then
      var v := 1 + MAX_U256 - w as int;
      -v as i256
    else
      w as i256
  }
  // pure-end

  function fromI256(w: Int.i256): u256
  {
    if w < 0 then
      var v := 1 + MAX_U256 + w as int;
      v as u256
    else
      w as u256
  }
  // pure-end

  import opened Int
}
