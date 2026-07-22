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

end A12Kernel.Conformance.LegalCharset
