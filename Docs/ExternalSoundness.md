# External Soundness

## Disallow unsound elements on external methods



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

If we assume `ExternMethod == NativeMethod`:

```dafny
forall M: ExternMethod {


}
```


