# External Soundness

## Disallow unsound elements on external methods

This means 

## External Invariant

Disallowing any `requires` clauses ...

For every externally-accessible method signature:

```Dafny
forall M: ExternMethod :: initialHeapState() ==> M.requires()
```

### The initial heap state 

```dafny
forall M, M': ExternMethod :: M'.ensures() ==> M.requires()
```

```dafny
forall M: ExternMethod, N: NativeMethod :: N.requires() ==> M.requires()
```

In practice, it is difficult if not impossible to ensure that a method can be implemented in external code yet not invoked from external code.

If we assume `ExternMethod == NativeMethod`:

```dafny
forall M: ExternMethod {


}
```


