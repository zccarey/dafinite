// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1 {
  export provides T, Equal, Foo

  type T(==) = seq<real>

  predicate Equal(u: T, v: T)
  {
    u == v
  }

  lemma Foo()
    ensures forall u, v :: Equal(u, v) ==> u == v  // bug was that errors reported here, but only if called from M2
  {}
}

module M2 {
  import M1

  lemma Bar()
  {
    var u: M1.T;
    var v: M1.T;
    assume M1.Equal(u, v);
    M1.Foo();
    assert u == v;
  }
}
