// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M()
{
  var _ := set x <- 5;
  var _ := set x <- 5;
  
}