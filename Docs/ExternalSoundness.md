# External Soundness

## Background

We are in the process of building multiple implementations of the AWS Encryption SDK (ESDK) for multiple programming languages in 2020. Our implementation strategy is to implement the majority of the library in Dafny, with a minimal shim of code in each target language to wrap the Dafny implementation with a safe and relatively idiomatic API.

This is somewhat uncharted territory for Dafny: it has excelled for years at verifying properties of entirely self-contained Dafny programs, especially in an educational context, but this is one of if not the first case of releasing production software based on it. Although Dafny includes an `{:extern}` attribute that enables external code to link with Dafny in various contexts, it introduces potential unsoundness if the external code does not actually match the Dafny specification. To date, the attribute has largely been used to include trusted internal implementations, so the risk and impact of unsoundness has been somewhat minimized. Our project, however, must allow for customer code to both invoke Dafny code and implement Dafny extension points.

The impact of unsoundness becomes severe in this case. If a Dafny method declares a parameter of type `Foo`, for example, where `Foo` is a Dafny class, then Dafny will not allow passing a `null` value as an argument. Once this method is compiled to a target language such as C#, however, C# will allow `null` to be passed. This can lead to errors and undefined behaviour deep within the Dafny runtime, potentially far from the source of the error if the `null` value is stored and referenced at a later time. These issues will lead to a bad customer experience as it will not be clear that their code is at fault, which in turn will lead to increased operational load for our team in order to support such customers.

## Requirements

1. The Dafny compiler should reject unsound programs involving external declarations by default as much as possible.
1. It must be possible to attach unproven assumptions to external code. The fact that these assumptions are unproven shoudl be as explicit as possible, to aid in understanding and tracking potential technical debt.
1. We should aim to minimize the amount of manual shim code we have to write in each target language, as this directly affects the scalability of our approach.
1. The errors we provide to customers when their code violates requirements should be as clear as possible, ideally allowing them to understand the error by only referring to the target language API documentation and not the underlying Dafny source code.
1. (Nice to have) We would be happier with a solution that allows us to separate Dafny and target language source code cleanly, such that the latter can be developed, tested and built with standard tooling for each language.

## Out of Scope

*
*
*

## Issues and Alternatives

The `{:extern}` attribute is currently quite overloaded. It can be applied to modules, traits, classes, methods and functions, and in most cases its effect is only to ensure that the names of these elements are preserved by the compiler, so that external code can reference them in some way. The details of how Dafny-generated code and manually-written external code are combined is largely left up to the specific target language. See Dafny GitHub issue [#469](https://github.com/dafny-lang/dafny/issues/469) for details.

The biggest threat to soundness is that most Dafny guarantees are checked statically. A fundamental feature of Dafny is pre- and post-conditions, expressed using `requires` and `ensures` declarations respectively.

(*** A bit about limiting the scope of what is external? ***)

We should first distiguish between two different cases of linkage with external code:

1. *External* methods, referring to methods that external code is able to invoke.
1. *Native* methods, referring to methods that are implemented in external code.

Currently, external methods may be invoked without necessarily satisfying their pre-conditions ([#461](https://github.com/dafny-lang/dafny/issues/461)) and the implementation of native methods may not necessarily satisfy their post-conditions ([#463](https://github.com/dafny-lang/dafny/issues/461)).

(*** Justify combining these concepts? ***)

Most issues can be addressed by forbidding all elements of Dafny method declarations that cannot be directly compiled to elements in the target language:

1. Disallow subtypes as in or out parameters.
1. Disallow preconditions 

### Object Invariants

```dafny
class Foo {

  invariant Valid()

}
```

## One-Way Doors

There are two major categories of one-way doors, corresponding to the two aspects that are the most difficult to modify: the public API of the ESDK implementations we release and the semantics of the Dafny language itself.

## Impact

## Assumptions

## Open Questions

* (make new version of :extern or whatever on by default in Dafny 3.0?)

## Appendices


### Disallow references to non-extern compiled elements

### Disallow unsound elements on external methods

This means 

## External Invariant

Disallowing any `requires` clauses ...

For every externally-accessible method signature:

```Dafny
forall m: ExternMethod :: initialHeapState() ==> m.requires()
```

### The initial heap state 

Since external code will be able to invoke external Dafny methods in any arbitrary order, the state of the Dafny heap after any one method must satisfy the requirements of all such methods. So:

```dafny
forall m, m': ExternMethod :: m'.ensures() ==> m.requires()
```

Since native implementations will be able to turn around and invoke any externally-invokable method:

```dafny
forall m: ExternMethod, n: NativeMethod :: n.requires() ==> m.requires()
```

In practice, it is difficult if not impossible to ensure that a method can be implemented in external code yet not invoked from external code. For example, it is natural for a Dafny code base to define a trait that is compiled to a C# interface, which can then be implemented using a C# class. There is nothing to stop other client code from creating this class and invoking its methods.

If we assume `ExternMethod == NativeMethod`:

```dafny
forall m: ExternMethod :: m.requires() ==> m.ensures() && m.ensures() ==> m.requires()
```

*Note*: applying invariant to input values of external methods. Pro of straight quantification approach.

## Singleton objects