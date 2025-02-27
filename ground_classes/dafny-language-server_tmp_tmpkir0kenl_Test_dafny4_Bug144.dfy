// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate p(i:int)

method m1()

method m2()
{
    assume exists i :: p(i);
    assert exists i :: p(i);
    m1();
    assert exists i :: p(i); // FAILS
}

class Test
{
        var arr : array<int>;
        predicate p(i: int)
        method foo()
                requires this.arr.Length > 0
                modifies this.arr
        {
                assume exists i :: this.p(i);
                this.arr[0] := 1;
                assert exists i :: this.p(i);  // FAILS
        }
}
