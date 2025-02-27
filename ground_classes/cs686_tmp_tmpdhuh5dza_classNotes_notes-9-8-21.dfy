class Secret {
  var secret: int
  var known: bool
  var count: int

  method Init(x: int)
    // pre-conditions-start
    requires 1 <= x <= 10
    // pre-conditions-end
    // post-conditions-start
    modifies `secret, `known, `count
    ensures this.secret == x
    ensures this.known == false
    ensures this.count == 0
    // post-conditions-end
  {
  // impl-start
    this.known := false;
    this.count := 0;
    this.secret := x;
  // impl-end
  }

  method Guess(g: int) returns (result: bool, guesses: int)
    // pre-conditions-start
    requires this.known == false
    // pre-conditions-end
    // post-conditions-start
    modifies `known, `count
    ensures if g == this.secret then result == true && this.known == true else result == false && this.known == false
    ensures this.count == old(this.count) + 1 && guesses == this.count
    // post-conditions-end
  {
  // impl-start
    if g == this.secret {
      this.known := true;
      result := true;
    } else {
      result := false;
    }
    this.count := this.count + 1;
    guesses := this.count;
  // impl-end
  }
}
