import A12Kernel.Elaboration.TemporalDistinctCount

/-! # A12Kernel.Conformance.TemporalDistinctCount — the component-set gate, against its neighbour

`NumberOfDifferentValues` and `FieldValuesNotUnique` accept the same operand shapes and gate them
differently, so every row here is paired with the neighbour's answer on the identical list. That
pairing is the point: a gate that merely *looked* right on this operator would be indistinguishable
from the neighbour's until a pair separates them, and one such pair exists
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-distinct-count-component-set-and-locus),
nine `rule check` rows in one batch).

The fixture's component sets agree with each declaration's format, which is what any model this
project admits looks like; a declaration whose format and components contradict each other is
refused by the stored-text classifiers and its authorability is unmeasured.
-/

namespace A12Kernel.Conformance.TemporalDistinctCount

open A12Kernel

private def yearMonth : TemporalComponents :=
  { year := true, month := true, day := false
    hour := false, minute := false, second := false }

private def dateField (id : FieldId) (name format : String)
    (components : TemporalComponents := TemporalComponents.fullDate) :
    FlatFieldDecl := {
  id
  groupPath := ["Probe"]
  name
  policy := { kind := .temporal .date components }
  temporalTargetPolicy := some { format }
}

private def model : FlatModel := {
  fields := [
    dateField 1 "FiledOn" "yyyy-MM-dd",
    dateField 2 "ClosedOn" "dd.MM.yyyy",
    dateField 3 "CoverFrom" "yyyy-MM" yearMonth,
    dateField 6 "SupersededFrom" "yyyy-MM-dd",
    { id := 4, groupPath := ["Probe"], name := "SkuText",
      policy := { kind := .string } },
    { id := 5, groupPath := ["Probe"], name := "Flag",
      policy := { kind := .boolean } }]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def pair (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

/-- This operator's verdict on one authored pair. -/
private def distinct? (first second : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalDistinctCountSource model ["Probe"] (pair first second) with
  | .ok _ => none
  | .error error => error.diagnostic?

private def distinctAdmitted (first second : String) : Bool :=
  (elaborateTemporalDistinctCountSource model ["Probe"] (pair first second)).toOption.isSome

/-- The neighbouring operator's verdict on the identical list. -/
private def unique? (first second : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalValuesNotUniqueSource model ["Probe"] (pair first second) with
  | .ok _ => none
  | .error error => error.diagnostic?

/- **The separating pair, and the reason this operator needs its own gate at all.** Two DATE fields
   naming the same components in different spellings are admitted here and refused by the neighbour.
   Adopting the neighbour's format-equality gate would have over-rejected this row — the inverse of
   the over-admission this project usually guards against, and the reason a measured neighbour is
   not a licence. -/
example :
    distinctAdmitted "FiledOn" "ClosedOn" = true ∧
      unique? "FiledOn" "ClosedOn" = some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- **A differing component set is refused, which is what keeps the gate from being vacuous.** The
   admitted row above and this one differ only in the second operand's component set, so a gate that
   admitted everything would satisfy the first and fail here. The Kernel's message names both
   formats rather than the sets, which is why the error carries formats. -/
example : distinct? "FiledOn" "CoverFrom" = some .dateFormatsNotCompatible := by
  native_decide

/- **Date-first with a non-temporal member draws the cross-family class**, not the component-set one:
   the kind gate runs before the list's own gate, so an operand that is not temporal at all never
   reaches the component comparison. -/
example : distinct? "FiledOn" "SkuText" = some .dateAndNonDate := by
  native_decide

/- **The kind-domain code is this operator's, one token from the neighbour's.** A Boolean draws
   `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED` here and the `CMP_`-less form there, on the same
   list. The two codes name different operators' gates and neither may be read off the other; this
   row exists because the names invite exactly that carry-over. -/
example :
    distinct? "Flag" "FiledOn" = some .onlyStringEnumNumberCmpDateAllowed ∧
      unique? "Flag" "FiledOn" = some .onlyStringEnumNumberDateAllowed ∧
      KernelStaticDiagnostic.onlyStringEnumNumberCmpDateAllowed.kernelCode
        = "MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED" ∧
      KernelStaticDiagnostic.onlyStringEnumNumberDateAllowed.kernelCode
        = "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED" := by
  native_decide

/- **Two distinct fields sharing one format are admitted by both operators**, which is what fixes
   the separation above as being about the *spelling* rather than about carrying two operands. It is
   also the row that dissolves the neighbour's refusal: its code names kinds, but the gate is the
   format string, and holding the format fixed while varying nothing else shows it. -/
example :
    distinctAdmitted "FiledOn" "SupersededFrom" = true ∧
      unique? "FiledOn" "SupersededFrom" = none := by
  native_decide

end A12Kernel.Conformance.TemporalDistinctCount
