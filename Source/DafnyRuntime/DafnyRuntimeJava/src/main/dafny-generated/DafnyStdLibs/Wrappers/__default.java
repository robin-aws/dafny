// Class __default
// Dafny class __default compiled into Java
package DafnyStdLibs.Wrappers;

import DafnyStdLibs.BoundedInts.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__E> OutcomeResult<__E> Need(dafny.TypeDescriptor<__E> _td___E, boolean condition, __E error)
  {
    if (condition) {
      return DafnyStdLibs.Wrappers.OutcomeResult.<__E>create_Pass_k(_td___E);
    } else {
      return DafnyStdLibs.Wrappers.OutcomeResult.<__E>create_Fail_k(_td___E, error);
    }
  }
  @Override
  public java.lang.String toString() {
    return "DafnyStdLibs.Wrappers._default";
  }
}
