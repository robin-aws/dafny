// RUN: %dafny /compile:0 /unicodeChar:0 "%s" > "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:cs "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:java "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:js "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:go "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:cpp "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// The following example should produce a compilation error, since there's
// an abstract type. It should not, however, crash.

type Opaque(0) // compilation error: this is an abstract type

datatype E = E(Opaque)

method N() returns (e: E) {
}

method Main() {
  var e := N();
  print e, "\n";
}
