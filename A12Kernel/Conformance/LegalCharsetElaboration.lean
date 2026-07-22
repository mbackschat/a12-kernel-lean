import A12Kernel.Elaboration.LegalCharset

/-! # A12Kernel.Conformance.LegalCharsetElaboration — supported-character definition locks

The supplied cluster classifier represents the source-owned Java `\\X` admission capability. These cases lock definition discrimination and the narrow ambiguous-overlap gate.
-/

namespace A12Kernel.Conformance.LegalCharsetElaboration

open A12Kernel

private def acute : String := "\u0301"
private def grave : String := "\u0300"
private def cedilla : String := "\u0327"
private def eAcute : String := "e\u0301"
private def eGrave : String := "e\u0300"
private def qAcute : String := "q\u0301"
private def rGrave : String := "r\u0300"

private def clustersOf (value : String) : List String :=
  if value == eAcute then [eAcute]
  else if value == eGrave then [eGrave]
  else if value == qAcute then [qAcute]
  else if value == rGrave then [rGrave]
  else if value == qAcute ++ "r" then [qAcute, "r"]
  else if value == eAcute ++ "x" then [eAcute, "x"]
  else value.toList.map (fun character => String.ofList [character])

private def accepts (entries : List String) (value : String) : Bool :=
  match admitSupportedCharacters clustersOf entries with
  | .ok charset => charset.accepts value
  | .error _ => false

private def definitionError? (entries : List String) :
    Option SupportedCharactersDefinitionError :=
  match admitSupportedCharacters clustersOf entries with
  | .ok _ => none
  | .error problem => some problem

/- Empty configuration selects the default, while accepted ranges and atoms lower to the runtime scanner. -/
example : accepts [] "café" = true := by
  native_decide

example : accepts [] "x😀" = false := by
  native_decide

example : accepts ["A-Z", eAcute] ("A" ++ eAcute ++ "Z") = true := by
  native_decide

example : accepts [eAcute, eGrave] (eAcute ++ eGrave) = true := by
  native_decide

example :
    accepts [eAcute, eAcute ++ "x"] (eAcute ++ "x" ++ eAcute) = true := by
  native_decide

/- Every bounded definition discriminator fails before runtime matching. -/
example : definitionError? [""] = some (.emptyEntry 0) := by
  native_decide

example : definitionError? ["😀"] = some (.surrogateBearingEntry 0) := by
  native_decide

example :
    definitionError? ["e" ++ acute ++ grave ++ cedilla] =
      some (.entryTooLong 0) := by
  native_decide

example : definitionError? ["ab"] = some (.plainMultiCharacterEntry 0) := by
  native_decide

example : definitionError? ["Z-A"] = some (.reversedRange 0) := by
  native_decide

example :
    definitionError? [qAcute ++ "r", qAcute, rGrave] =
      some (.ambiguousOverlap 0) := by
  native_decide

end A12Kernel.Conformance.LegalCharsetElaboration
