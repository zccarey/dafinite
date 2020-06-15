// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma lemma_Subset_Cardinalities<I>(a : set<I>, b : set<I>)
  ensures a <= b ==> |a| <= |b| && |b - a| == |b| - |a|
{
  if (a <= b) {
    if x :| x in a {
      assert x in b;
      lemma_Subset_Cardinalities(a - {x}, b - {x});
    }
    else {
      assert a == {};
      assert |b - a| == |b| == |b| - |a|;
    }
  }
}

predicate pred_lemma_Subset_Cardinalities<I>(a : set<I>, b : set<I>) 
  ensures a <= b ==> |a| <= |b| && |b - a| == |b| - |a|
  ensures pred_lemma_Subset_Cardinalities(a, b) 
{
  lemma_Subset_Cardinalities(a, b);
  true
}

lemma lemma_Subset_Cardinalities_Universal<I>()
  ensures forall a : set<I>, b : set<I> :: a <= b ==> pred_lemma_Subset_Cardinalities(a, b) && |a| <= |b| && |b - a| == |b| - |a|
{
}

lemma lemma_Subset_Cardinalities_Universal2<I>()
  ensures forall a : set<I>, b : set<I> :: a <= b ==> |a| <= |b| && |b - a| == |b| - |a|
{
  if a : set<I>, b : set<I> :| a <= b && !(|a| <= |b| && |b - a| == |b| - |a|) {
        assert pred_lemma_Subset_Cardinalities(a, b);
  }
}
