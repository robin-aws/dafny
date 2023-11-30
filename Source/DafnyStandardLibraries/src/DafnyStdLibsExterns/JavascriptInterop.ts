// @ts-nocheck

export module JavascriptInterop {
  // Boolean

  export function IsTrue(o) {
    return o == true;
  }
  
  // Numbers
  
  // TODO: Should be partial functions instead

  export function AsInt(o) {
    return BigInt(o ? o : -1);
  }

  export function FromInt(o) {
    return o;
  }

  // Strings

  export function AsString(o) {
    return typeof o == "string" ? o : null;
  }

  export function ToString(o) {
    return o;
    // for --unicode-char
    // return _dafny.Seq.UnicodeFromString(o);
  }

  export function FromString(o) {
    return o;
    // for --unicode-char
    // return o.toVerbatimString(false);
  }

  // Objects

  export function AsObject(o) {
    return typeof o == "object" ? o : null;
  }
  
  export function GetProperties(o) {
    return Object.keys(o).map(name => ToString(name));
  }
  
  export function HasProperty(o, m) {
    const name = FromString(m);
    return name in o;
  }

  export function GetProperty(o, m) {
    const name = FromString(m);
    return o[name];
  }

  export function GetOptProperty(o, m) {
    if (o == null) {
      return undefined;
    }
    const name = FromString(m);
    return o[name];
  }

  export function SetProperty(o, m, v) {
    const name = FromString(m);
    o[name] = v;
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