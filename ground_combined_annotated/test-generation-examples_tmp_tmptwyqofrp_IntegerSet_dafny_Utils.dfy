

module Utils {
  class Assertions<T> {
    static method {:extern} assertEquals(expected: T, actual: T)
      // pre-conditions-start
      requires expected == actual
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end

    static method {:extern} expectEquals(expected: T, actual: T)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures expected == actual
      // post-conditions-end

    static method {:extern} assertTrue(condition: bool)
      // pre-conditions-start
      requires condition
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end

    static method {:extern} expectTrue(condition: bool)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures condition
      // post-conditions-end

    static method {:extern} assertFalse(condition: bool)
      // pre-conditions-start
      requires !condition
      // pre-conditions-end
      // post-conditions-start
      // post-conditions-end

    static method {:extern} expectFalse(condition: bool)
      // pre-conditions-start
      // pre-conditions-end
      // post-conditions-start
      ensures !condition
      // post-conditions-end
  }
}
