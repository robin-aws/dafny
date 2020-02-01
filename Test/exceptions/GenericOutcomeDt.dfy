// Does not test anything Exceptions-related, but is included by other tests
// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype GenericOutcome<T> =
| GenericSuccess(value: T)
| GenericFailure(error: string)
{
    predicate method IsFailure() {
        this.GenericFailure?
    }
    function method PropagateFailure(): GenericOutcome<T> requires IsFailure() {
        this
    }
    function method Extract(): T requires !IsFailure() {
        this.value
    }
}
