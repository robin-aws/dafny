include "./ListUser.dfy"

module ListTest {
  import opened Collections
  import opened ListUser

  method Main() {
    var myList := new ArrayList();
    myList.Add(1);
    myList.Add(2);
    myList.Add(3);
    var sum := Sum(myList);
    print "sum=", sum, "\n";
  }
}