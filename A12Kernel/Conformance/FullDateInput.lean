import A12Kernel.Elaboration.FullDateInput

/-! # Full-Date stored-input conformance locks -/

namespace A12Kernel.Conformance.FullDateInput

open A12Kernel

private def dateField (format : String)
    (partialMode : TemporalPartialMode := .full)
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id := 1
  groupPath := ["Policy"]
  name := "EffectiveDate"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format, partialMode, youngerThan1900Check }
}

private def classifyResult? (field : FlatFieldDecl) (zone text : String) :
    Option (FullDateInputError ⊕ RawCell) := do
  let checked ← (certifyFullDateInputField field).toOption
  pure <| match checked.classifyStoredForModel zone text with
    | .error error => .inl error
    | .ok raw => .inr raw

private def certificationError? (field : FlatFieldDecl) : Option CanonicalFullDateFieldError :=
  match certifyFullDateInputField field with
  | .error error => some error
  | .ok _ => none

private def utcDate? (year : Int) (month day : Nat) : Option RawCell := do
  let full ← FullDate.ofYmd? year month day
  let localDateTime ← LocalDateTime.ofDateHms? full 0 0 0
  pure (.parsed (.temporal (.date {
    instant := localDateTime.resolveUtc
    parts := full.civil.parts
    basis := .storedGregorian
  })))

example :
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "2024-06-15" =
      (utcDate? 2024 6 15).map .inr ∧
    classifyResult? (dateField "yyyy-MM-dd") "GMT" "2024-06-15" =
      (utcDate? 2024 6 15).map .inr ∧
    classifyResult? (dateField "dd.MM.yyyy") "UTC" "15.06.2024" =
      (utcDate? 2024 6 15).map .inr := by native_decide

example :
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "15.06.2024" =
      some (.inr (.rejected .dateFormat)) ∧
    classifyResult? (dateField "dd.MM.yyyy") "UTC" "2024-06-15" =
      some (.inr (.rejected .dateFormat)) ∧
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "1583-02-30" =
      some (.inr (.rejected .dateFormat)) ∧
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "1582-10-10" =
      some (.inr (.rejected .dateFormat)) := by native_decide

example :
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "1583-10-15" =
      some (.inr (.rejected .dateInvalid)) ∧
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "1500-02-29" =
      some (.inr (.rejected .dateInvalid)) ∧
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "1583-10-16" =
      (utcDate? 1583 10 16).map .inr ∧
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "2024-13-01" =
      some (.inr (.rejected .dateFormat)) := by native_decide

example :
    classifyResult? (dateField "yyyy-MM-dd") "UTC" "1899-12-31" =
      (utcDate? 1899 12 31).map .inr ∧
    classifyResult? (dateField "yyyy-MM-dd" .full true) "UTC" "1899-12-31" =
      some (.inr (.rejected .dateInvalid)) ∧
    classifyResult? (dateField "yyyy-MM-dd" .full true) "UTC" "1900-01-01" =
      (utcDate? 1900 1 1).map .inr := by native_decide

example : classifyResult? (dateField "yyyy-MM-dd") "UTC" "" =
    some (.inr .presentEmpty) := by native_decide

example :
    let value? zone := (classifyResult? (dateField "yyyy-MM-dd")
      zone "2024-01-01").bind Sum.getRight?
    let utc := value? "UTC"
    let berlin := value? "Europe/Berlin"
    (utc.bind fun raw => match raw with
      | .parsed (.temporal (.date value)) => some value
      | _ => none).map (fun value => (value.parts, value.basis, value.instant)) =
        some ({ year := 2024, month := 1, day := 1 },
          .storedGregorian, { epochMillis := 1704067200000 }) ∧
    (berlin.bind fun raw => match raw with
      | .parsed (.temporal (.date value)) => some value
      | _ => none).map (fun value => (value.parts, value.basis, value.instant)) =
        some ({ year := 2024, month := 1, day := 1 },
          .storedGregorian, { epochMillis := 1704063600000 }) := by native_decide

example : classifyResult? (dateField "yyyy-MM-dd") "Europe/Paris" "2024-01-01" =
    some (.inl (.unsupportedZone "Europe/Paris")) := by native_decide

example :
    let path := ["Policy", "EffectiveDate"]
    let incomplete := { TemporalComponents.fullDate with day := false }
    certificationError?
        { dateField "yyyy-MM-dd" with policy := { kind := .string } } =
      some (.notFullDate path .string) ∧
    certificationError? { dateField "yyyy-MM-dd" with
        policy := { kind := .temporal .date incomplete } } =
      some (.notFullDate path (.temporal .date incomplete)) ∧
    certificationError?
        { dateField "yyyy-MM-dd" with temporalTargetPolicy := none } =
      some (.policyUnavailable path) ∧
    certificationError? (dateField "yyyy/MM/dd") =
      some (.unsupportedPolicy path "yyyy/MM/dd" .full) ∧
    certificationError? (dateField "yyyy-MM-dd" .dayOptional) =
      some (.unsupportedPolicy path "yyyy-MM-dd" .dayOptional) := by native_decide

example :
    FormalCause.dateFormat.fixedFormalErrorCode? =
      some "datumFormatFalsch" ∧
    FormalCause.dateInvalid.fixedFormalErrorCode? = some "datumFalsch" := by native_decide

end A12Kernel.Conformance.FullDateInput
