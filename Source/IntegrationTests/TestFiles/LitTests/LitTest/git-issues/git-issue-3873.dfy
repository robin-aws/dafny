// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
  var a := new ()[1];
  var m: map<array<()>, ()> := map[a := ()];
  var v :| v in m;
  print v[0], "\n";
}
