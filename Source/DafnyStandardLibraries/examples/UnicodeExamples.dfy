
/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UnicodeExamples {
  module BaseExamples {
    import opened DafnyStdLibs.Unicode.Base
    import opened Helpers

    const TEST_ASSIGNED_PLANE_CODE_POINTS: set<CodePoint> := {
      0x000055,  // Latin capital letter U
      0x01F11D,  // Parenthesized Latin capital letter N
      0x02053C,  // CJK unified ideograph 𠔼
      0x030256,  // CJK unified ideograph 𰉖
      0x0E004F,  // Tag Latin capital letter O
      0x0FDDDD,  // arbitrary code point in Private Use Area-A
      0x10EEEE   // arbitrary code point in Private Use Area-B
    }

    lemma LemmaAssignedCodePoints()
      ensures forall p | p in TEST_ASSIGNED_PLANE_CODE_POINTS :: IsInAssignedPlane(p)
    {
      reveal IsInAssignedPlane();
    }

    method {:test} TestAssignedCodePoints() {
      LemmaAssignedCodePoints();
      AssertAndExpect(forall p | p in TEST_ASSIGNED_PLANE_CODE_POINTS :: IsInAssignedPlane(p));
    }
  }

  module Utf8EncodingFormExamples {
    import opened DafnyStdLibs.Unicode.Base
    import opened DafnyStdLibs.Unicode.Utf8EncodingForm
    import opened DafnyStdLibs.Wrappers
    import opened Helpers

    method {:test} TestEmptySequenceIsWellFormed() {
      expect IsWellFormedCodeUnitSequence([]);
    }

    const TEST_SCALAR_VALUES: seq<(ScalarValue, WellFormedCodeUnitSeq)> := [
      // One byte: dollar sign
      (0x0024, [0x24]),
      // Two bytes: pound sign
      (0x00A3, [0xC2, 0xA3]),
      // Three bytes: euro sign
      (0x20AC, [0xE2, 0x82, 0xAC]),
      // Four bytes: money bag emoji
      (0x1F4B0, [0xF0, 0x9F, 0x92, 0xB0])
    ]

    method {:test} TestEncodeDecodeScalarValue() {
      for i := 0 to |TEST_SCALAR_VALUES| {
        var pair := TEST_SCALAR_VALUES[i];
        AssertAndExpect(EncodeScalarValue(pair.0) == pair.1);
        AssertAndExpect(DecodeCodeUnitSequence(pair.1) == [pair.0]);
        AssertAndExpect(DecodeCodeUnitSequenceChecked(pair.1) == Some([pair.0]));
      }
    }

    method {:test} TestEmptySequenceIsNotMinimalWellFormed() {
      expect !IsMinimalWellFormedCodeUnitSubsequence([]);
    }

    method {:test} TestMinimalWellFormedCodeUnitSubsequences() {
      for i := 0 to |TEST_SCALAR_VALUES| {
        var pair := TEST_SCALAR_VALUES[i];
        expect IsMinimalWellFormedCodeUnitSubsequence(pair.1);
      }
    }

    // Examples taken from description of Table 3-7.
    const TEST_ILL_FORMED_SEQUENCES: seq<CodeUnitSeq> := [
      // C0 is not well-formed as a first byte
      [0xC0, 0xAF],
      // 9F is not well-formed as a second byte when E0 is a well-formed first byte
      [0xE0, 0x9F, 0x80]
    ]

    method {:test} TestDecodeIllFormedSequence() {
      for i := 0 to |TEST_ILL_FORMED_SEQUENCES| {
        var s := TEST_ILL_FORMED_SEQUENCES[i];
        AssertAndExpect(DecodeCodeUnitSequenceChecked(s).None?);
      }
    }
  }

  module Utf16EncodingFormExamples {
    import opened DafnyStdLibs.Unicode.Base
    import opened DafnyStdLibs.Unicode.Utf16EncodingForm
    import opened DafnyStdLibs.Wrappers
    import opened Helpers

    method {:test} TestEmptySequenceIsWellFormed() {
      expect IsWellFormedCodeUnitSequence([]);
    }

    const TEST_SCALAR_VALUES: seq<(ScalarValue, WellFormedCodeUnitSeq)> := [
      // One code unit: dollar sign
      (0x0024, [0x0024]),
      // Two code units: money bag emoji
      (0x1F4B0, [0xD83D, 0xDCB0])
    ]

    method {:test} TestEncodeDecodeScalarValue() {
      for i := 0 to |TEST_SCALAR_VALUES| {
        var pair := TEST_SCALAR_VALUES[i];
        AssertAndExpect(EncodeScalarValue(pair.0) == pair.1);
        AssertAndExpect(DecodeCodeUnitSequence(pair.1) == [pair.0]);
        AssertAndExpect(DecodeCodeUnitSequenceChecked(pair.1) == Some([pair.0]));
      }
    }

    method {:test} TestEmptySequenceIsNotMinimalWellFormed() {
      expect !IsMinimalWellFormedCodeUnitSubsequence([]);
    }

    method {:test} TestMinimalWellFormedCodeUnitSubsequences() {
      for i := 0 to |TEST_SCALAR_VALUES| {
        var pair := TEST_SCALAR_VALUES[i];
        expect IsMinimalWellFormedCodeUnitSubsequence(pair.1);
      }
    }

    // Because surrogate code points are not Unicode scalar values, isolated UTF-16 code units in the range
    // D800_16 .. DFFF_16 are ill-formed. (Section 3.9 D91)
    const TEST_ILL_FORMED_SEQUENCES: seq<CodeUnitSeq> := [
      [0xD800],
      [0xDABC],
      [0xDFFF]
    ]

    method {:test} TestDecodeIllFormedSequence() {
      for i := 0 to |TEST_ILL_FORMED_SEQUENCES| {
        var s := TEST_ILL_FORMED_SEQUENCES[i];
        AssertAndExpect(DecodeCodeUnitSequenceChecked(s).None?);
      }
    }
  }

  module UnicodeStringsWithUnicodeCharExamples {
    import opened DafnyStdLibs.BoundedInts
    import opened DafnyStdLibs.Unicode.Base
    import opened DafnyStdLibs.Wrappers
    import opened Helpers

    import UnicodeStrings = DafnyStdLibs.Unicode.UnicodeStringsWithUnicodeChar

    const currenciesStr := "\U{24}\U{A3}\U{20AC}\U{1F4B0}"
    const currenciesUtf8: seq<uint8> := [0x24] + [0xC2, 0xA3] + [0xE2, 0x82, 0xAC] + [0xF0, 0x9F, 0x92, 0xB0]
    const currenciesUtf16: seq<uint16> := [0x0024] + [0x00A3] + [0x20AC] + [0xD83D, 0xDCB0]

    method {:test} TestToUTF8Checked() {
      expect UnicodeStrings.ToUTF8Checked(currenciesStr) == Some(currenciesUtf8);
    }

    method {:test} TestFromUTF8Checked() {
      expect UnicodeStrings.FromUTF8Checked(currenciesUtf8) == Some(currenciesStr);
      expect UnicodeStrings.FromUTF8Checked(currenciesUtf8[2..]) == None;
    }

    method {:test} TestToUTF16() {
      expect UnicodeStrings.ToUTF16Checked(currenciesStr) == Some(currenciesUtf16);
    }

    method {:test} TestFromUTF16Checked() {
      expect UnicodeStrings.FromUTF16Checked(currenciesUtf16) == Some(currenciesStr);
      expect UnicodeStrings.FromUTF16Checked(currenciesUtf16[..|currenciesUtf16| - 1]) == None;
    }

    method {:test} TestASCIIToUnicode() {
      expect UnicodeStrings.ASCIIToUTF8("foobar") == [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72];
      expect UnicodeStrings.ASCIIToUTF16("foobar") == [0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72];
    }
  }

  module Utf8EncodingSchemeExamples {
    import opened DafnyStdLibs.Unicode.Base
    import opened DafnyStdLibs.Unicode.Utf8EncodingForm
    import EncodingScheme = DafnyStdLibs.Unicode.Utf8EncodingScheme
    import opened DafnyStdLibs.Wrappers
    import opened Helpers

    const currenciesUtf8: CodeUnitSeq := [0x24] + [0xC2, 0xA3] + [0xE2, 0x82, 0xAC] + [0xF0, 0x9F, 0x92, 0xB0]

    method {:test} TestSerializeDeserialize() {
      expect EncodingScheme.Deserialize(EncodingScheme.Serialize(currenciesUtf8)) == currenciesUtf8;
    }
  }
}
