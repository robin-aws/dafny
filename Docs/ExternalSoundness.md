# External Soundness

## Background

We are in the process of building multiple implementations of the AWS Encryption SDK (ESDK) for multiple programming languages in 2020. Our implementation strategy is to implement the majority of the library in Dafny, with a minimal shim of code in each target language to wrap the Dafny implementation with a safe and relatively idiomatic API.

This is somewhat uncharted territory for Dafny: it has excelled for years at verifying properties of entirely self-contained Dafny programs, especially in an educational context, but this is one of if not the first case of releasing production software based on it. Although Dafny includes an `{:extern}` attribute that enables external code to link with Dafny in various contexts, it introduces potential unsoundness if the external code does not actually match the Dafny specification. To date, the attribute has largely been used to include trusted internal implementations, so the risk and impact of unsoundness has been somewhat minimized. Our project, however, must allow for customer code to both invoke Dafny code and implement Dafny extension points.

The impact of unsoundness becomes severe in this case. If a Dafny method declares a parameter of type `Foo`, for example, where `Foo` is a Dafny class, then Dafny will not allow passing a `null` value as an argument. Once this method is compiled to a target language such as C#, however, C# will allow `null` to be passed. This can lead to errors and undefined behaviour deep within the Dafny runtime, potentially far from the source of the error if the `null` value is stored and referenced at a later time. These issues will lead to a bad customer experience as it will not be clear that their code is at fault, which in turn will lead to increased operational load for our team in order to support such customers. It also undermines customer trust to tout the advantages of applying formal verification to our code base, only to ship bugs in the shim code.

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



(*** A bit about limiting the scope of what is external? ***)

We should first distiguish between two different cases of linkage with external code, for the sake of consistent terminology:

1. *Exposed* methods, referring to methods that external code is able to invoke.
1. *Native* methods, referring to methods that may be implemented in external code.

In practice, it is difficult if not impossible to ensure that a method can be implemented in external code yet not invoked from external code. For example, it is natural for a Dafny code base to define a trait that is compiled to a C# interface, which can then be implemented using a C# class. There is nothing to stop other C# client code from creating this class and invoking its methods. In addition, there will be frequent use cases for methods that need to support both external invocation and native implementations anyway, such as the `List` example in this doc. Therefore, we propose focussing on this use case first. This is a two-way door: we can always support sound external-only or native-only methods in a future release of Dafny with looser restrictions, if this turns out to be strongly desired.

(*** CONNECT ***)

Most issues can be addressed by forbidding all elements of Dafny method declarations that cannot be directly compiled to elements in the target language, as shown below.

### Disallow types not directly supports by the target language/runtime

This includes not only most subtypes but also `newtype` declarations that do not match a built-in type such as `int` exactly. Allowing a bounded type such as `newtype MyType = x | -100 <= x < 0x8000_0000` that compiles to a type such as `int` still introduces unsoundness, since external code could return `-1000`.

### Require all reference types used as in or out parameters are nullable (i.e. `Foo?` rather than just `Foo`).

This is a corrolary of the previous statement, since many reference types in Dafny source code are implicitly non-null subtypes.

### Disallow almost all preconditions and postconditions.

The attentive reader will likely be surprised by the "almost" in the title of this section.

The biggest threat to soundness is that most Dafny guarantees are checked statically. A fundamental feature of Dafny is pre- and post-conditions, expressed using `requires` and `ensures` declarations respectively. Currently, external methods may be invoked without necessarily satisfying their pre-conditions ([#461](https://github.com/dafny-lang/dafny/issues/461)) and the implementation of native methods may not necessarily satisfy their post-conditions ([#463](https://github.com/dafny-lang/dafny/issues/461)).



### External Invariants

Many other programming languages ensure object invariants through a combination of access control (making fields private so that all access and mutation happens only within a bounded set of methods) and concurrency control (to ensure only one thread can ever observe an object in an invalid state at one time). This ensures that objects are valid by default. Dafny instead approaches this by validating that any operation that requires an object to be valid (which in practice is nearly all of them) provides proof that this is true, based on the context of the operation. Thus Dafny objects are assumed invalid unless proven valid.

Because of this, disallowing all preconditions on external methods is extremely limiting: it means that absolutely nothing can be assumed about any Dafny objects in the control flow of external methods. It is often not possible to dynamically verify a predicate such as `Valid()` since it usually refers to ghost state, and even if it was possible would often be prohibitively expensive. It is also dangerous, however, to allow external methods to assume objects are in a `Valid()` state without proof, for the same reasons that we cannot allow stray `null` values to pollute the Dafny runtime.

If we assume and/or enforce certain invariants about the linkage between Dafny and external code, however, it is possible allow very specific pre- and post-conditions on external methods. Let's assume for the moment that Dafny objects can only be modified through Dafny methods, and not directly by external code referencing the internals of compiled code directly. This means if a predicate that reads some subset of the Dafny heap holds when control is passed to external code, it will remain true whenever Dafny code begins to execute again.

We can consider the implications while abusing Dafny notation. Since external code will be able to invoke exposed Dafny methods in any arbitrary order, the state of the Dafny heap after any one method must satisfy the requirements of all such methods. So:

```dafny
forall m: ExposedMethod, m': ExposedMethod :: m'.ensures() ==> m.requires()
```

Since native implementations will be able to turn around and invoke any externally-invokable method:

```dafny
forall m: ExposedMethod, n: NativeMethod :: n.requires() ==> m.requires()
```

If we make the simplifying assumption above that `ExposedMethod == NativeMethod` and label both as *external methods*, we have:

```dafny
forall m: ExternalMethod, m': ExternalMethod :: m'.requires() ==> m.requires() && m.ensures() ==> m.requires()
```

Therefore the pre-condition of every exposed method must be equivalent, and the post-condition of every such method must imply this pre-condition. We can refer to this single predicate as the *external invariant*. Although we may not know exactly what to make it, we at least know that the Dafny verifer should enforce that for every external method, its pre-condition must be equal to this invariant, and its post-condition at least as strong. That is:

```dafny
exists p: bool ::
  forall m: ExternMethod :: m.requires() == p && m.ensures() ==> p
```

### Defining the External Invariant

The question is now what

### Disallow references to non-extern compiled elements

### Supports traits extending other traits

## One-Way Doors

There are two major categories of one-way doors, corresponding to the two aspects that are the most difficult to modify: the public API of the ESDK implementations we release and the semantics of the Dafny language itself.

## Impact

## Assumptions

## Open Questions

* (make new version of :extern or whatever on by default in Dafny 3.0?)
* (Termination??)

## Appendices

*Note*: applying invariant to input values of external methods. Pro of straight quantification approach.

## Singleton objects