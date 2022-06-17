
// RUN: %dafny /compile:0 /useRuntimeLib /spillTargetCode:3 /out:%S/../Library %S/../Library/Halver.dfy
// RUN: dotnet build %S/../Library

// RUN: %dafny /compile:0 /useRuntimeLib /spillTargetCode:3 %s
// RUN: dotnet run %S > "%t"
// RUN: %diff "%s.expect" "%t"

include "../Library/bin/Debug/net6.0/Library.dll"

module ConsumerModule {

  import opened LibraryModule

  method Main() {
    var twoN := 42;
    var N := Halve(twoN);
    print "Half of ", twoN, " is ", N, "\n";
  }
}