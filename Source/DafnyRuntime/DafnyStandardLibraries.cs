// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

#if ISDAFNYRUNTIMELIB
using System;
using System.Numerics;
using System.Collections;
#endif

namespace DafnyStdLibs.Functions {

} // end of namespace DafnyStdLibs.Functions
namespace DafnyStdLibs.Relations {

} // end of namespace DafnyStdLibs.Relations
namespace DafnyStdLibs.Wrappers {

  public partial class __default {
    public static DafnyStdLibs.Wrappers._IOutcomeResult<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return DafnyStdLibs.Wrappers.OutcomeResult<__E>.create_Pass_k();
      } else {
        return DafnyStdLibs.Wrappers.OutcomeResult<__E>.create_Fail_k(error);
      }
    }
  }

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    bool IsFailure();
    DafnyStdLibs.Wrappers._IOption<__U> PropagateFailure<__U>();
    T Extract();
    DafnyStdLibs.Wrappers._IResult<T, __E> ToResult<__E>(__E error);
    DafnyStdLibs.Wrappers._IOutcome<__E> ToOutcome<__E>(__E error);
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() {
    }
    public static DafnyStdLibs.Wrappers._IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IOption<T>>(DafnyStdLibs.Wrappers.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d)._value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public bool IsFailure() {
      return (this).is_None;
    }
    public DafnyStdLibs.Wrappers._IOption<__U> PropagateFailure<__U>() {
      return DafnyStdLibs.Wrappers.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
    public static T GetOr(DafnyStdLibs.Wrappers._IOption<T> _this, T @default) {
      DafnyStdLibs.Wrappers._IOption<T> _source0 = _this;
      if (_source0.is_None) {
        return @default;
      } else {
        T _0___mcc_h0 = _source0.dtor_value;
        T _1_v = _0___mcc_h0;
        return _1_v;
      }
    }
    public DafnyStdLibs.Wrappers._IResult<T, __E> ToResult<__E>(__E error) {
      DafnyStdLibs.Wrappers._IOption<T> _source1 = this;
      if (_source1.is_None) {
        return DafnyStdLibs.Wrappers.Result<T, __E>.create_Failure(error);
      } else {
        T _2___mcc_h0 = _source1.dtor_value;
        T _3_v = _2___mcc_h0;
        return DafnyStdLibs.Wrappers.Result<T, __E>.create_Success(_3_v);
      }
    }
    public DafnyStdLibs.Wrappers._IOutcome<__E> ToOutcome<__E>(__E error) {
      DafnyStdLibs.Wrappers._IOption<T> _source2 = this;
      if (_source2.is_None) {
        return DafnyStdLibs.Wrappers.Outcome<__E>.create_Fail(error);
      } else {
        T _4___mcc_h0 = _source2.dtor_value;
        T _5_v = _4___mcc_h0;
        return DafnyStdLibs.Wrappers.Outcome<__E>.create_Pass();
      }
    }
    public static __FC Map<__FC>(DafnyStdLibs.Wrappers._IOption<T> _this, Func<DafnyStdLibs.Wrappers._IOption<T>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<DafnyStdLibs.Wrappers._IOption<T>, __FC>>(rewrap)(_this);
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() : base() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _value;
    public Option_Some(T @value) : base() {
      this._value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.Option_Some<T>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out R, out E> {
    bool is_Success { get; }
    bool is_Failure { get; }
    R dtor_value { get; }
    E dtor_error { get; }
    _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1);
    bool IsFailure();
    DafnyStdLibs.Wrappers._IResult<__U, E> PropagateFailure<__U>();
    R Extract();
    DafnyStdLibs.Wrappers._IOption<R> ToOption();
    DafnyStdLibs.Wrappers._IOutcome<E> ToOutcome();
  }
  public abstract class Result<R, E> : _IResult<R, E> {
    public Result() {
    }
    public static DafnyStdLibs.Wrappers._IResult<R, E> Default(R _default_R) {
      return create_Success(_default_R);
    }
    public static Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IResult<R, E>> _TypeDescriptor(Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IResult<R, E>>(DafnyStdLibs.Wrappers.Result<R, E>.Default(_td_R.Default()));
    }
    public static _IResult<R, E> create_Success(R @value) {
      return new Result_Success<R, E>(@value);
    }
    public static _IResult<R, E> create_Failure(E error) {
      return new Result_Failure<R, E>(error);
    }
    public bool is_Success { get { return this is Result_Success<R, E>; } }
    public bool is_Failure { get { return this is Result_Failure<R, E>; } }
    public R dtor_value {
      get {
        var d = this;
        return ((Result_Success<R, E>)d)._value;
      }
    }
    public E dtor_error {
      get {
        var d = this;
        return ((Result_Failure<R, E>)d)._error;
      }
    }
    public abstract _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1);
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public DafnyStdLibs.Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return DafnyStdLibs.Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
    public R Extract() {
      return (this).dtor_value;
    }
    public static R GetOr(DafnyStdLibs.Wrappers._IResult<R, E> _this, R @default) {
      DafnyStdLibs.Wrappers._IResult<R, E> _source3 = _this;
      if (_source3.is_Success) {
        R _6___mcc_h0 = _source3.dtor_value;
        R _7_s = _6___mcc_h0;
        return _7_s;
      } else {
        E _8___mcc_h1 = _source3.dtor_error;
        E _9_e = _8___mcc_h1;
        return @default;
      }
    }
    public DafnyStdLibs.Wrappers._IOption<R> ToOption() {
      DafnyStdLibs.Wrappers._IResult<R, E> _source4 = this;
      if (_source4.is_Success) {
        R _10___mcc_h0 = _source4.dtor_value;
        R _11_s = _10___mcc_h0;
        return DafnyStdLibs.Wrappers.Option<R>.create_Some(_11_s);
      } else {
        E _12___mcc_h1 = _source4.dtor_error;
        E _13_e = _12___mcc_h1;
        return DafnyStdLibs.Wrappers.Option<R>.create_None();
      }
    }
    public DafnyStdLibs.Wrappers._IOutcome<E> ToOutcome() {
      DafnyStdLibs.Wrappers._IResult<R, E> _source5 = this;
      if (_source5.is_Success) {
        R _14___mcc_h0 = _source5.dtor_value;
        R _15_s = _14___mcc_h0;
        return DafnyStdLibs.Wrappers.Outcome<E>.create_Pass();
      } else {
        E _16___mcc_h1 = _source5.dtor_error;
        E _17_e = _16___mcc_h1;
        return DafnyStdLibs.Wrappers.Outcome<E>.create_Fail(_17_e);
      }
    }
    public static __FC Map<__FC>(DafnyStdLibs.Wrappers._IResult<R, E> _this, Func<DafnyStdLibs.Wrappers._IResult<R, E>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<DafnyStdLibs.Wrappers._IResult<R, E>, __FC>>(rewrap)(_this);
    }
    public static DafnyStdLibs.Wrappers._IResult<R, __NewE> MapFailure<__NewE>(DafnyStdLibs.Wrappers._IResult<R, E> _this, Func<E, __NewE> reWrap) {
      DafnyStdLibs.Wrappers._IResult<R, E> _source6 = _this;
      if (_source6.is_Success) {
        R _18___mcc_h0 = _source6.dtor_value;
        R _19_s = _18___mcc_h0;
        return DafnyStdLibs.Wrappers.Result<R, __NewE>.create_Success(_19_s);
      } else {
        E _20___mcc_h1 = _source6.dtor_error;
        E _21_e = _20___mcc_h1;
        return DafnyStdLibs.Wrappers.Result<R, __NewE>.create_Failure(Dafny.Helpers.Id<Func<E, __NewE>>(reWrap)(_21_e));
      }
    }
  }
  public class Result_Success<R, E> : Result<R, E> {
    public readonly R _value;
    public Result_Success(R @value) : base() {
      this._value = @value;
    }
    public override _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1) {
      if (this is _IResult<__R, __E> dt) { return dt; }
      return new Result_Success<__R, __E>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.Result_Success<R, E>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<R, E> : Result<R, E> {
    public readonly E _error;
    public Result_Failure(E error) : base() {
      this._error = error;
    }
    public override _IResult<__R, __E> DowncastClone<__R, __E>(Func<R, __R> converter0, Func<E, __E> converter1) {
      if (this is _IResult<__R, __E> dt) { return dt; }
      return new Result_Failure<__R, __E>(converter1(_error));
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.Result_Failure<R, E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<out E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    DafnyStdLibs.Wrappers._IOutcome<E> PropagateFailure();
    DafnyStdLibs.Wrappers._IOption<__R> ToOption<__R>(__R r);
    DafnyStdLibs.Wrappers._IResult<__R, E> ToResult<__R>(__R r);
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() {
    }
    public static DafnyStdLibs.Wrappers._IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IOutcome<E>>(DafnyStdLibs.Wrappers.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d)._error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public DafnyStdLibs.Wrappers._IOutcome<E> PropagateFailure() {
      return this;
    }
    public DafnyStdLibs.Wrappers._IOption<__R> ToOption<__R>(__R r) {
      DafnyStdLibs.Wrappers._IOutcome<E> _source7 = this;
      if (_source7.is_Pass) {
        return DafnyStdLibs.Wrappers.Option<__R>.create_Some(r);
      } else {
        E _22___mcc_h0 = _source7.dtor_error;
        E _23_e = _22___mcc_h0;
        return DafnyStdLibs.Wrappers.Option<__R>.create_None();
      }
    }
    public DafnyStdLibs.Wrappers._IResult<__R, E> ToResult<__R>(__R r) {
      DafnyStdLibs.Wrappers._IOutcome<E> _source8 = this;
      if (_source8.is_Pass) {
        return DafnyStdLibs.Wrappers.Result<__R, E>.create_Success(r);
      } else {
        E _24___mcc_h0 = _source8.dtor_error;
        E _25_e = _24___mcc_h0;
        return DafnyStdLibs.Wrappers.Result<__R, E>.create_Failure(_25_e);
      }
    }
    public static __FC Map<__FC>(DafnyStdLibs.Wrappers._IOutcome<E> _this, Func<DafnyStdLibs.Wrappers._IOutcome<E>, __FC> rewrap) {
      return Dafny.Helpers.Id<Func<DafnyStdLibs.Wrappers._IOutcome<E>, __FC>>(rewrap)(_this);
    }
    public static DafnyStdLibs.Wrappers._IResult<__T, __NewE> MapFailure<__T, __NewE>(DafnyStdLibs.Wrappers._IOutcome<E> _this, Func<E, __NewE> rewrap, __T @default)
    {
      DafnyStdLibs.Wrappers._IOutcome<E> _source9 = _this;
      if (_source9.is_Pass) {
        return DafnyStdLibs.Wrappers.Result<__T, __NewE>.create_Success(@default);
      } else {
        E _26___mcc_h0 = _source9.dtor_error;
        E _27_e = _26___mcc_h0;
        return DafnyStdLibs.Wrappers.Result<__T, __NewE>.create_Failure(Dafny.Helpers.Id<Func<E, __NewE>>(rewrap)(_27_e));
      }
    }
    public static DafnyStdLibs.Wrappers._IOutcome<E> Need(bool condition, E error)
    {
      if (condition) {
        return DafnyStdLibs.Wrappers.Outcome<E>.create_Pass();
      } else {
        return DafnyStdLibs.Wrappers.Outcome<E>.create_Fail(error);
      }
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() : base() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E _error;
    public Outcome_Fail(E error) : base() {
      this._error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.Outcome_Fail<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcomeResult<out E> {
    bool is_Pass_k { get; }
    bool is_Fail_k { get; }
    E dtor_error { get; }
    _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    DafnyStdLibs.Wrappers._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class OutcomeResult<E> : _IOutcomeResult<E> {
    public OutcomeResult() {
    }
    public static DafnyStdLibs.Wrappers._IOutcomeResult<E> Default() {
      return create_Pass_k();
    }
    public static Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IOutcomeResult<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<DafnyStdLibs.Wrappers._IOutcomeResult<E>>(DafnyStdLibs.Wrappers.OutcomeResult<E>.Default());
    }
    public static _IOutcomeResult<E> create_Pass_k() {
      return new OutcomeResult_Pass_k<E>();
    }
    public static _IOutcomeResult<E> create_Fail_k(E error) {
      return new OutcomeResult_Fail_k<E>(error);
    }
    public bool is_Pass_k { get { return this is OutcomeResult_Pass_k<E>; } }
    public bool is_Fail_k { get { return this is OutcomeResult_Fail_k<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((OutcomeResult_Fail_k<E>)d)._error;
      }
    }
    public abstract _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail_k;
    }
    public DafnyStdLibs.Wrappers._IResult<__U, E> PropagateFailure<__U>() {
      return DafnyStdLibs.Wrappers.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class OutcomeResult_Pass_k<E> : OutcomeResult<E> {
    public OutcomeResult_Pass_k() : base() {
    }
    public override _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcomeResult<__E> dt) { return dt; }
      return new OutcomeResult_Pass_k<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.OutcomeResult_Pass_k<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.OutcomeResult.Pass'";
      return s;
    }
  }
  public class OutcomeResult_Fail_k<E> : OutcomeResult<E> {
    public readonly E _error;
    public OutcomeResult_Fail_k(E error) : base() {
      this._error = error;
    }
    public override _IOutcomeResult<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcomeResult<__E> dt) { return dt; }
      return new OutcomeResult_Fail_k<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as DafnyStdLibs.Wrappers.OutcomeResult_Fail_k<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers.OutcomeResult.Fail'";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }
} // end of namespace DafnyStdLibs.Wrappers
namespace DafnyStdLibs {

} // end of namespace DafnyStdLibs
namespace _module {

  public partial class __default {
    public static void HasTuples()
    {
      bool _28_b;
      _28_b = true;
      _System._ITuple0 _29_has0;
      _29_has0 = _System.Tuple0.create();
      _System._ITuple1<bool> _30_has1;
      _30_has1 = _System.Tuple1<bool>.create(_28_b);
      _System._ITuple2<bool, bool> _31_has2;
      _31_has2 = _System.Tuple2<bool, bool>.create(_28_b, _28_b);
      _System._ITuple3<bool, bool, bool> _32_has3;
      _32_has3 = _System.Tuple3<bool, bool, bool>.create(_28_b, _28_b, _28_b);
      _System._ITuple4<bool, bool, bool, bool> _33_has4;
      _33_has4 = _System.Tuple4<bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b);
      _System._ITuple5<bool, bool, bool, bool, bool> _34_has5;
      _34_has5 = _System.Tuple5<bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple6<bool, bool, bool, bool, bool, bool> _35_has6;
      _35_has6 = _System.Tuple6<bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple7<bool, bool, bool, bool, bool, bool, bool> _36_has7;
      _36_has7 = _System.Tuple7<bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple8<bool, bool, bool, bool, bool, bool, bool, bool> _37_has8;
      _37_has8 = _System.Tuple8<bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple9<bool, bool, bool, bool, bool, bool, bool, bool, bool> _38_has9;
      _38_has9 = _System.Tuple9<bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple10<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _39_has10;
      _39_has10 = _System.Tuple10<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple11<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _40_has11;
      _40_has11 = _System.Tuple11<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple12<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _41_has12;
      _41_has12 = _System.Tuple12<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple13<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _42_has13;
      _42_has13 = _System.Tuple13<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple14<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _43_has14;
      _43_has14 = _System.Tuple14<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple15<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _44_has15;
      _44_has15 = _System.Tuple15<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple16<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _45_has16;
      _45_has16 = _System.Tuple16<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple17<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _46_has17;
      _46_has17 = _System.Tuple17<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple18<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _47_has18;
      _47_has18 = _System.Tuple18<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple19<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _48_has19;
      _48_has19 = _System.Tuple19<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
      _System._ITuple20<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool> _49_has20;
      _49_has20 = _System.Tuple20<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool>.create(_28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b, _28_b);
    }
    public static void HasArrows()
    {
      Func<BigInteger> _50_has0;
      _50_has0 = ((System.Func<BigInteger>)(() => {
        return new BigInteger(42);
      }));
      Func<bool, BigInteger> _51_has1;
      _51_has1 = ((System.Func<bool, BigInteger>)((_52_x1) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, BigInteger> _53_has2;
      _53_has2 = ((System.Func<bool, bool, BigInteger>)((_54_x1, _55_x2) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, BigInteger> _56_has3;
      _56_has3 = ((System.Func<bool, bool, bool, BigInteger>)((_57_x1, _58_x2, _59_x3) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, BigInteger> _60_has4;
      _60_has4 = ((System.Func<bool, bool, bool, bool, BigInteger>)((_61_x1, _62_x2, _63_x3, _64_x4) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, BigInteger> _65_has5;
      _65_has5 = ((System.Func<bool, bool, bool, bool, bool, BigInteger>)((_66_x1, _67_x2, _68_x3, _69_x4, _70_x5) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, BigInteger> _71_has6;
      _71_has6 = ((System.Func<bool, bool, bool, bool, bool, bool, BigInteger>)((_72_x1, _73_x2, _74_x3, _75_x4, _76_x5, _77_x6) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, BigInteger> _78_has7;
      _78_has7 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_79_x1, _80_x2, _81_x3, _82_x4, _83_x5, _84_x6, _85_x7) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _86_has8;
      _86_has8 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_87_x1, _88_x2, _89_x3, _90_x4, _91_x5, _92_x6, _93_x7, _94_x8) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _95_has9;
      _95_has9 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_96_x1, _97_x2, _98_x3, _99_x4, _100_x5, _101_x6, _102_x7, _103_x8, _104_x9) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _105_has10;
      _105_has10 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_106_x1, _107_x2, _108_x3, _109_x4, _110_x5, _111_x6, _112_x7, _113_x8, _114_x9, _115_x10) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _116_has11;
      _116_has11 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_117_x1, _118_x2, _119_x3, _120_x4, _121_x5, _122_x6, _123_x7, _124_x8, _125_x9, _126_x10, _127_x11) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _128_has12;
      _128_has12 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_129_x1, _130_x2, _131_x3, _132_x4, _133_x5, _134_x6, _135_x7, _136_x8, _137_x9, _138_x10, _139_x11, _140_x12) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _141_has13;
      _141_has13 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_142_x1, _143_x2, _144_x3, _145_x4, _146_x5, _147_x6, _148_x7, _149_x8, _150_x9, _151_x10, _152_x11, _153_x12, _154_x13) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _155_has14;
      _155_has14 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_156_x1, _157_x2, _158_x3, _159_x4, _160_x5, _161_x6, _162_x7, _163_x8, _164_x9, _165_x10, _166_x11, _167_x12, _168_x13, _169_x14) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _170_has15;
      _170_has15 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_171_x1, _172_x2, _173_x3, _174_x4, _175_x5, _176_x6, _177_x7, _178_x8, _179_x9, _180_x10, _181_x11, _182_x12, _183_x13, _184_x14, _185_x15) => {
        return new BigInteger(42);
      }));
      Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger> _186_has16;
      _186_has16 = ((System.Func<bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, bool, BigInteger>)((_187_x1, _188_x2, _189_x3, _190_x4, _191_x5, _192_x6, _193_x7, _194_x8, _195_x9, _196_x10, _197_x11, _198_x12, _199_x13, _200_x14, _201_x15, _202_x16) => {
        return new BigInteger(42);
      }));
    }
    public static void HasArrays()
    {
      byte _203_n;
      _203_n = (byte)(0);
      bool[] _204_has1;
      bool[] _nw0 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _204_has1 = _nw0;
      bool[,] _205_has2;
      bool[,] _nw1 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _205_has2 = _nw1;
      bool[,,] _206_has3;
      bool[,,] _nw2 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _206_has3 = _nw2;
      bool[,,,] _207_has4;
      bool[,,,] _nw3 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _207_has4 = _nw3;
      bool[,,,,] _208_has5;
      bool[,,,,] _nw4 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _208_has5 = _nw4;
      bool[,,,,,] _209_has6;
      bool[,,,,,] _nw5 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _209_has6 = _nw5;
      bool[,,,,,,] _210_has7;
      bool[,,,,,,] _nw6 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _210_has7 = _nw6;
      bool[,,,,,,,] _211_has8;
      bool[,,,,,,,] _nw7 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _211_has8 = _nw7;
      bool[,,,,,,,,] _212_has9;
      bool[,,,,,,,,] _nw8 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _212_has9 = _nw8;
      bool[,,,,,,,,,] _213_has10;
      bool[,,,,,,,,,] _nw9 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _213_has10 = _nw9;
      bool[,,,,,,,,,,] _214_has11;
      bool[,,,,,,,,,,] _nw10 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _214_has11 = _nw10;
      bool[,,,,,,,,,,,] _215_has12;
      bool[,,,,,,,,,,,] _nw11 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _215_has12 = _nw11;
      bool[,,,,,,,,,,,,] _216_has13;
      bool[,,,,,,,,,,,,] _nw12 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _216_has13 = _nw12;
      bool[,,,,,,,,,,,,,] _217_has14;
      bool[,,,,,,,,,,,,,] _nw13 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _217_has14 = _nw13;
      bool[,,,,,,,,,,,,,,] _218_has15;
      bool[,,,,,,,,,,,,,,] _nw14 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _218_has15 = _nw14;
      bool[,,,,,,,,,,,,,,,] _219_has16;
      bool[,,,,,,,,,,,,,,,] _nw15 = new bool[Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit"), Dafny.Helpers.ToIntChecked(_203_n, "array size exceeds memory limit")];
      _219_has16 = _nw15;
    }
  }

  public partial class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _module
