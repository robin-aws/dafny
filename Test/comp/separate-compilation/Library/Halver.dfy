module LibraryModule {

  function method Halve(x: nat): nat
    requires x % 2 == 0
  {
    x / 2
  }

}