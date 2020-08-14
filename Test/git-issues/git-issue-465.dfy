// RUN: dafny /rprint:foo-resolved.dfy /printMode:DllEmbed "%s" > "%t"
// RUN: cat foo-resolved.dfy >> "%t"
// RUN: dafny foo-resolved.dfy >> "%t"
// RUN: rm foo-resolved.dfy
// RUN: %diff "%s.expect" "%t"

module Foo {
  datatype Bar = Bar {}
}

module Foo2 {
  import Foo
  const bar := Foo.Bar;
}

method Main() {
  print Foo2.bar, "\n";
}

