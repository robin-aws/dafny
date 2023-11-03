// Dafny program the_program compiled into JavaScript
let DafnyStdLibs_BoundedInts = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "DafnyStdLibs.BoundedInts._default";
    }
    _parentTraits() {
      return [];
    }
    static get TWO__TO__THE__8() {
      return new BigNumber(256);
    };
    static get TWO__TO__THE__16() {
      return new BigNumber(65536);
    };
    static get TWO__TO__THE__32() {
      return new BigNumber(4294967296);
    };
    static get TWO__TO__THE__64() {
      return new BigNumber("18446744073709551616");
    };
    static get TWO__TO__THE__128() {
      return new BigNumber("340282366920938463463374607431768211456");
    };
    static get TWO__TO__THE__7() {
      return new BigNumber(128);
    };
    static get TWO__TO__THE__15() {
      return new BigNumber(32768);
    };
    static get TWO__TO__THE__31() {
      return new BigNumber(2147483648);
    };
    static get TWO__TO__THE__63() {
      return new BigNumber("9223372036854775808");
    };
    static get TWO__TO__THE__127() {
      return new BigNumber("170141183460469231731687303715884105728");
    };
    static get TWO__TO__THE__0() {
      return _dafny.ONE;
    };
    static get TWO__TO__THE__1() {
      return new BigNumber(2);
    };
    static get TWO__TO__THE__2() {
      return new BigNumber(4);
    };
    static get TWO__TO__THE__4() {
      return new BigNumber(16);
    };
    static get TWO__TO__THE__5() {
      return new BigNumber(32);
    };
    static get TWO__TO__THE__24() {
      return new BigNumber(16777216);
    };
    static get TWO__TO__THE__40() {
      return new BigNumber(1099511627776);
    };
    static get TWO__TO__THE__48() {
      return new BigNumber(281474976710656);
    };
    static get TWO__TO__THE__56() {
      return new BigNumber("72057594037927936");
    };
    static get TWO__TO__THE__256() {
      return new BigNumber("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    };
    static get TWO__TO__THE__512() {
      return new BigNumber("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    };
  };

  $module.uint8 = class uint8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.uint16 = class uint16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.uint32 = class uint32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.uint64 = class uint64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.uint128 = class uint128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.int8 = class int8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.int16 = class int16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.int32 = class int32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.int64 = class int64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.int128 = class int128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.nat8 = class nat8 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.nat16 = class nat16 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.nat32 = class nat32 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static *IntegerRange(lo, hi) {
      while (lo.isLessThan(hi)) {
        yield lo.toNumber();
        lo = lo.plus(1);
      }
    }
    static get Default() {
      return 0;
    }
  };

  $module.nat64 = class nat64 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };

  $module.nat128 = class nat128 {
    constructor () {
    }
    _parentTraits() {
      return [];
    }
    static get Default() {
      return _dafny.ZERO;
    }
  };
  return $module;
})(); // end of module DafnyStdLibs_BoundedInts
let DafnyStdLibs_Functions = (function() {
  let $module = {};

  return $module;
})(); // end of module DafnyStdLibs_Functions
let DafnyStdLibs_Relations = (function() {
  let $module = {};

  return $module;
})(); // end of module DafnyStdLibs_Relations
let DafnyStdLibs_Wrappers = (function() {
  let $module = {};

  $module.__default = class __default {
    constructor () {
      this._tname = "DafnyStdLibs.Wrappers._default";
    }
    _parentTraits() {
      return [];
    }
    static Need(condition, error) {
      if (condition) {
        return DafnyStdLibs_Wrappers.OutcomeResult.create_Pass_k();
      } else {
        return DafnyStdLibs_Wrappers.OutcomeResult.create_Fail_k(error);
      }
    };
  };

  $module.Option = class Option {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_None() {
      let $dt = new Option(0);
      return $dt;
    }
    static create_Some(value) {
      let $dt = new Option(1);
      $dt.value = value;
      return $dt;
    }
    get is_None() { return this.$tag === 0; }
    get is_Some() { return this.$tag === 1; }
    get dtor_value() { return this.value; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.Option.None";
      } else if (this.$tag === 1) {
        return "Wrappers.Option.Some" + "(" + _dafny.toString(this.value) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.value, other.value);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return DafnyStdLibs_Wrappers.Option.create_None();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Option.Default();
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_None;
    };
    PropagateFailure() {
      let _this = this;
      return DafnyStdLibs_Wrappers.Option.create_None();
    };
    Extract() {
      let _this = this;
      return (_this).dtor_value;
    };
    GetOr(_$$_default) {
      let _this = this;
      let _source0 = _this;
      if (_source0.is_None) {
        return _$$_default;
      } else {
        let _0___mcc_h0 = (_source0).value;
        let _1_v = _0___mcc_h0;
        return _1_v;
      }
    };
    ToResult(error) {
      let _this = this;
      let _source1 = _this;
      if (_source1.is_None) {
        return DafnyStdLibs_Wrappers.Result.create_Failure(error);
      } else {
        let _2___mcc_h0 = (_source1).value;
        let _3_v = _2___mcc_h0;
        return DafnyStdLibs_Wrappers.Result.create_Success(_3_v);
      }
    };
    ToOutcome(error) {
      let _this = this;
      let _source2 = _this;
      if (_source2.is_None) {
        return DafnyStdLibs_Wrappers.Outcome.create_Fail(error);
      } else {
        let _4___mcc_h0 = (_source2).value;
        let _5_v = _4___mcc_h0;
        return DafnyStdLibs_Wrappers.Outcome.create_Pass();
      }
    };
    Map(rewrap) {
      let _this = this;
      return (rewrap)(_this);
    };
  }

  $module.Result = class Result {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Success(value) {
      let $dt = new Result(0);
      $dt.value = value;
      return $dt;
    }
    static create_Failure(error) {
      let $dt = new Result(1);
      $dt.error = error;
      return $dt;
    }
    get is_Success() { return this.$tag === 0; }
    get is_Failure() { return this.$tag === 1; }
    get dtor_value() { return this.value; }
    get dtor_error() { return this.error; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.Result.Success" + "(" + _dafny.toString(this.value) + ")";
      } else if (this.$tag === 1) {
        return "Wrappers.Result.Failure" + "(" + _dafny.toString(this.error) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0 && _dafny.areEqual(this.value, other.value);
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.error, other.error);
      } else  {
        return false; // unexpected
      }
    }
    static Default(_default_R) {
      return DafnyStdLibs_Wrappers.Result.create_Success(_default_R);
    }
    static Rtd(rtd$_R) {
      return class {
        static get Default() {
          return Result.Default(rtd$_R.Default);
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_Failure;
    };
    PropagateFailure() {
      let _this = this;
      return DafnyStdLibs_Wrappers.Result.create_Failure((_this).dtor_error);
    };
    Extract() {
      let _this = this;
      return (_this).dtor_value;
    };
    GetOr(_$$_default) {
      let _this = this;
      let _source3 = _this;
      if (_source3.is_Success) {
        let _6___mcc_h0 = (_source3).value;
        let _7_s = _6___mcc_h0;
        return _7_s;
      } else {
        let _8___mcc_h1 = (_source3).error;
        let _9_e = _8___mcc_h1;
        return _$$_default;
      }
    };
    ToOption() {
      let _this = this;
      let _source4 = _this;
      if (_source4.is_Success) {
        let _10___mcc_h0 = (_source4).value;
        let _11_s = _10___mcc_h0;
        return DafnyStdLibs_Wrappers.Option.create_Some(_11_s);
      } else {
        let _12___mcc_h1 = (_source4).error;
        let _13_e = _12___mcc_h1;
        return DafnyStdLibs_Wrappers.Option.create_None();
      }
    };
    ToOutcome() {
      let _this = this;
      let _source5 = _this;
      if (_source5.is_Success) {
        let _14___mcc_h0 = (_source5).value;
        let _15_s = _14___mcc_h0;
        return DafnyStdLibs_Wrappers.Outcome.create_Pass();
      } else {
        let _16___mcc_h1 = (_source5).error;
        let _17_e = _16___mcc_h1;
        return DafnyStdLibs_Wrappers.Outcome.create_Fail(_17_e);
      }
    };
    Map(rewrap) {
      let _this = this;
      return (rewrap)(_this);
    };
    MapFailure(reWrap) {
      let _this = this;
      let _source6 = _this;
      if (_source6.is_Success) {
        let _18___mcc_h0 = (_source6).value;
        let _19_s = _18___mcc_h0;
        return DafnyStdLibs_Wrappers.Result.create_Success(_19_s);
      } else {
        let _20___mcc_h1 = (_source6).error;
        let _21_e = _20___mcc_h1;
        return DafnyStdLibs_Wrappers.Result.create_Failure((reWrap)(_21_e));
      }
    };
  }

  $module.Outcome = class Outcome {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Pass() {
      let $dt = new Outcome(0);
      return $dt;
    }
    static create_Fail(error) {
      let $dt = new Outcome(1);
      $dt.error = error;
      return $dt;
    }
    get is_Pass() { return this.$tag === 0; }
    get is_Fail() { return this.$tag === 1; }
    get dtor_error() { return this.error; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.Outcome.Pass";
      } else if (this.$tag === 1) {
        return "Wrappers.Outcome.Fail" + "(" + _dafny.toString(this.error) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.error, other.error);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return DafnyStdLibs_Wrappers.Outcome.create_Pass();
    }
    static Rtd() {
      return class {
        static get Default() {
          return Outcome.Default();
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_Fail;
    };
    PropagateFailure() {
      let _this = this;
      return _this;
    };
    ToOption(r) {
      let _this = this;
      let _source7 = _this;
      if (_source7.is_Pass) {
        return DafnyStdLibs_Wrappers.Option.create_Some(r);
      } else {
        let _22___mcc_h0 = (_source7).error;
        let _23_e = _22___mcc_h0;
        return DafnyStdLibs_Wrappers.Option.create_None();
      }
    };
    ToResult(r) {
      let _this = this;
      let _source8 = _this;
      if (_source8.is_Pass) {
        return DafnyStdLibs_Wrappers.Result.create_Success(r);
      } else {
        let _24___mcc_h0 = (_source8).error;
        let _25_e = _24___mcc_h0;
        return DafnyStdLibs_Wrappers.Result.create_Failure(_25_e);
      }
    };
    Map(rewrap) {
      let _this = this;
      return (rewrap)(_this);
    };
    MapFailure(rewrap, _$$_default) {
      let _this = this;
      let _source9 = _this;
      if (_source9.is_Pass) {
        return DafnyStdLibs_Wrappers.Result.create_Success(_$$_default);
      } else {
        let _26___mcc_h0 = (_source9).error;
        let _27_e = _26___mcc_h0;
        return DafnyStdLibs_Wrappers.Result.create_Failure((rewrap)(_27_e));
      }
    };
    static Need(condition, error) {
      if (condition) {
        return DafnyStdLibs_Wrappers.Outcome.create_Pass();
      } else {
        return DafnyStdLibs_Wrappers.Outcome.create_Fail(error);
      }
    };
  }

  $module.OutcomeResult = class OutcomeResult {
    constructor(tag) {
      this.$tag = tag;
    }
    static create_Pass_k() {
      let $dt = new OutcomeResult(0);
      return $dt;
    }
    static create_Fail_k(error) {
      let $dt = new OutcomeResult(1);
      $dt.error = error;
      return $dt;
    }
    get is_Pass_k() { return this.$tag === 0; }
    get is_Fail_k() { return this.$tag === 1; }
    get dtor_error() { return this.error; }
    toString() {
      if (this.$tag === 0) {
        return "Wrappers.OutcomeResult.Pass'";
      } else if (this.$tag === 1) {
        return "Wrappers.OutcomeResult.Fail'" + "(" + _dafny.toString(this.error) + ")";
      } else  {
        return "<unexpected>";
      }
    }
    equals(other) {
      if (this === other) {
        return true;
      } else if (this.$tag === 0) {
        return other.$tag === 0;
      } else if (this.$tag === 1) {
        return other.$tag === 1 && _dafny.areEqual(this.error, other.error);
      } else  {
        return false; // unexpected
      }
    }
    static Default() {
      return DafnyStdLibs_Wrappers.OutcomeResult.create_Pass_k();
    }
    static Rtd() {
      return class {
        static get Default() {
          return OutcomeResult.Default();
        }
      };
    }
    IsFailure() {
      let _this = this;
      return (_this).is_Fail_k;
    };
    PropagateFailure() {
      let _this = this;
      return DafnyStdLibs_Wrappers.Result.create_Failure((_this).dtor_error);
    };
  }
  return $module;
})(); // end of module DafnyStdLibs_Wrappers
let DafnyStdLibs = (function() {
  let $module = {};

  return $module;
})(); // end of module DafnyStdLibs
