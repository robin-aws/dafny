using System.Text.RegularExpressions;

namespace TestDafny; 

public class InlineExpectedMessages {
  private readonly Regex Pattern = new Regex("\\s*//\\s*(\\^*)\\s(.*)");
  
  
}