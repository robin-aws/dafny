
// TIRED

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t" || true
// RUN: %dafny /noVerify /compile:4 /compileTarget:cpp "%s" >> "%t" || true
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t" || true
// RUN: %diff "%s.oldway.expect" "%t"

// WIRED

// RUN: %testdafny "%s"

iterator EmptyIterator() yields (r: bool) 
  ensures false
{}

method Main() {
  var i := new EmptyIterator();
  var more := i.MoveNext();
  expect !more;
  print "All done iterating!\n";
}