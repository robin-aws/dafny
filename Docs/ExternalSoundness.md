# External Invariants


For every externally-accessible method signature:

```Dafny
forall M: ExternMethod :: (initial heap state) ==> M.requires()
```

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




```