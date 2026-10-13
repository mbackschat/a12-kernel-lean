import A12Kernel.Semantics.LegalCharset

/-! # A12Kernel.Conformance.LegalCharset — admitted supported-character scan locks

These examples start with an already-admitted bounded charset and lock the pure whole-input scan plus the full-check formal-cause boundary.
-/

namespace A12Kernel.Conformance.LegalCharset

open A12Kernel

private def acute : Char := '\u0301'
private def grave : Char := '\u0300'
private def eAcute : String := "e\u0301"
private def eGrave : String := "e\u0300"

private def upper : LegalCharRange := { first := 'A', last := 'Z' }

private def atomicCharset : LegalCharset :=
  .restricted [upper] [.pair 'e' acute]

/- Default BMP accepts ordinary BMP scalars and rejects supplementary-plane input. -/
example : LegalCharset.defaultBmp.accepts "café" = true := by
  native_decide

example : LegalCharset.defaultBmp.accepts "x😀" = false := by
  native_decide

/- A configured combined entry is consumed atomically beside ordinary ranges. -/
example : atomicCharset.accepts ("A" ++ eAcute ++ "Z") = true := by
  native_decide

example : atomicCharset.accepts "Ae" = false := by
  native_decide

example : atomicCharset.accepts ("A" ++ String.ofList [acute]) = false := by
  native_decide

example : atomicCharset.accepts (String.ofList [acute] ++ "e") = false := by
  native_decide

example : atomicCharset.accepts (eAcute ++ String.ofList [acute]) = false := by
  native_decide

/- Shared prefixes remain distinct complete atoms and do not leak their components. -/
example :
    (.restricted [] [.pair 'e' acute, .pair 'e' grave] : LegalCharset).accepts
      (eAcute ++ eGrave) = true := by
  native_decide

/- A terminal prefix of a longer atom selects the longest complete match when it is present. -/
example :
    (.restricted [] [.pair 'e' acute, .triple 'e' acute 'x'] : LegalCharset).accepts
      (eAcute ++ "x" ++ eAcute) = true := by
  native_decide

example :
    (.restricted [] [.pair 'e' acute, .triple 'e' acute 'x'] : LegalCharset).accepts
      "x" = false := by
  native_decide

/- Empty input always terminates successfully, including for an explicitly empty restricted set. -/
example : (.restricted [] [] : LegalCharset).accepts "" = true := by
  decide

/- The full-check input stage reuses the ordinary unsupported-character cause. -/
example :
    (atomicCharset.checkRawText (.parsed "A😀")).findings =
      [.unsupportedCharacter] := by
  native_decide

/- The rejected-unit scan reports where `accepts` only stops: it keeps scanning after a rejected character, and a supplementary-plane scalar contributes both of its UTF-16 units. -/
example :
    (utf16CodeUnits 'A', utf16CodeUnits '\uFFFF', utf16CodeUnits (Char.ofNat 0x10000),
      utf16CodeUnits '😀', utf16CodeUnits (Char.ofNat 0x10FFFF)) =
      ([0x41], [0xFFFF], [0xD800, 0xDC00], [0xD83D, 0xDE00], [0xDBFF, 0xDFFF]) := by
  native_decide

example :
    (.restricted [upper] [] : LegalCharset).accepts "aBc" = false ∧
    restrictedRejectedUnits [upper] [] "aBc" = [0x61, 0x63] := by
  native_decide

example : restrictedRejectedUnits [upper] [] "A😀Z" = [0xD83D, 0xDE00] := by
  native_decide

/- A consumed atom contributes nothing, while a stranded atom component is rejected and the scan then resumes after it. -/
example :
    restrictedRejectedUnits [upper] [.pair 'e' acute] ("A" ++ eAcute ++ "Z") = [] ∧
    restrictedRejectedUnits [upper] [.pair 'e' acute] ("A" ++ String.ofList [acute] ++ "b") =
      [0x301, 0x62] := by
  native_decide

end A12Kernel.Conformance.LegalCharset
