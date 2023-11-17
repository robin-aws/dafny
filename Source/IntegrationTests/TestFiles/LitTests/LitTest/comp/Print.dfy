// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108 and https://github.com/dafny-lang/dafny/issues/2582
// RUN: %dafny /compile:0 /unicodeChar:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /unicodeChar:0 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Python salts hashes so they are not deterministic.

method Main() {
  PrintString();
}

method PrintString() {
  print "Strings in collections:\n";
  print "  ", ["abc", "def"], "\n";
  print "  ", [["abc", "def"]], "\n";
  print "  ", {"abc", "def"}, "\n";
  print "  ", [['a', 'b', 'c'], ['d', 'e', 'f']], "\n";
  var a : seq<seq<char>> := [[]];
  print "  ", a, "\n";
  var b : seq<char>;
  print "  ", [b], "\n";
  print "  ", [seq(5, x => 'a')], "\n";
}
