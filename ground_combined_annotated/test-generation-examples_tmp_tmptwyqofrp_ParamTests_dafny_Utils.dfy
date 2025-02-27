

module Utils {
  class Assertions {
    static method {:axiom} assertEquals<T>(left: T, right: T)
      // pre-conditions-start
      requires left == right
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end

    static method {:axiom} assertTrue(value: bool)
      // pre-conditions-start
      requires value
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end

    static method {:axiom} assertFalse(value: bool)
      // pre-conditions-start
      requires !value
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end
  }
}
