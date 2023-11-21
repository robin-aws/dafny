// @ts-nocheck

export module JavascriptInterop {
  // Boolean

  export function IsTrue(o) {
    return o == true;
  }
  
  // Numbers

  export function AsInt(o) {
    return typeof o == "number";
  }

  export function FromInt(o) {
    return typeof o == "number" ? o : 0;
  }

  export function IsUndefined(o) {
    return typeof o == "undefined";
  }

  // Strings

  export function AsString(o) {
    return typeof o == "string" ? o : null;
  }

  export function ToString(o) {
    return _dafny.UnicodeFromString(o);
  }

  export function FromString(o) {
    return o.toVerbatimString(false);
  }

  // Objects

  export function AsObject(o) {
    return typeof o == "object" ? o : null;
  }

  export function HasProperty(o, m) {
    return Object.hasOwnProperty(o, m);
  }

  export function GetProperty(o, m) {
    return o[m];
  }

  export function GetOptProperty(o, m) {
    return o[m];
  }

  export function SetProperty(o, m, v) {
    o[m] = v;
  }

  // Arrays

  export function AsArray(o) {
    // TODO: find the right definition for this, if it's useful,
    // since typeof returns "object"
    return o;
  }

  export function Length(o) {
    return o.length;
  }

  export function At(o, i) {
    return o[i];
  }

  export function ToSeq(o) {
    return new _dafny.Seq(...o);
  }

  export function FromSeq(o) {
    return o;
  }

  // Undefined

  export function Undefined() {
    return undefined;
  }

  export function IsUndefined(o) {
    return o == undefined;
  }

  // Testing only

  export function SampleString() {
    return "Hello world!";
  }

  export function SampleObject() {
    return {a: 1, b: {c: 6}, d: [1, 2, 3, {}], e: null};
  }
}