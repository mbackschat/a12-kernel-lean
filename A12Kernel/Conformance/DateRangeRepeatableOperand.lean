import A12Kernel.Elaboration.DateRangeBoundComparison
import A12Kernel.Elaboration.DateRangeStoredComparison
import A12Kernel.Elaboration.DateRangeOverlap

/-! # Rule-locus refusal locks for a repeatable DateRange operand

Every DateRange condition carrier reads its operand through one of two shared resolvers, so an
unstarred repeatable operand reached from a non-iterating rule locus is one refusal class rather
than four carrier-specific ones. These cases pin the Kernel diagnostic that class reports, on the
overlap predicate, stored range equality, an exact endpoint comparison, and a yearless endpoint.

The refusal's placement also fixes its order against the whole-rule error-field gate: the operand
fails while the condition is being elaborated, so no rule is ever assembled and the
error-field-referenced gate cannot report first. The Kernel agrees, and its rows are recorded with
the checkpoint that these cases replay; here that order is a consequence of the two-stage boundary
rather than a separate decision.
-/

namespace A12Kernel.Conformance.DateRangeRepeatableOperand

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd")
    (separator : String := "/") : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def fixed := rangeField 1 ["Form"] "Existing"
private def repeated := rangeField 2 ["Form", "Rows"] "RowRange" [10]
private def yearlessRepeated :=
  rangeField 3 ["Form", "Rows"] "RowMonths" [10] "MM" "/"

private def model : FlatModel := {
  fields := [fixed, repeated, yearlessRepeated]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 5 }]
}

private def overlapOperand (groups : List String) (field : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field }

private def overlapDiagnostic? (first rest : SurfaceFieldEntityOperand) :
    Option KernelStaticDiagnostic :=
  match elaborateDateRangesOverlapSource model ["Form"] { first, rest := [rest] } with
  | .ok _ => none
  | .error cause => cause.diagnostic?

/- The overlap predicate resolves its operands through the shared entity-list checker, so the
missing-wildcard class arrives there and does not depend on which slot holds the repeatable
operand. -/
example :
    overlapDiagnostic? (overlapOperand ["Form", "Rows"] "RowRange")
        (overlapOperand ["Form"] "Existing") = some .noWildcard ∧
      overlapDiagnostic? (overlapOperand ["Form"] "Existing")
        (overlapOperand ["Form", "Rows"] "RowRange") = some .noWildcard ∧
      overlapDiagnostic? (overlapOperand ["Form"] "Existing")
        (overlapOperand ["Form"] "Existing") ≠ some .noWildcard := by
  native_decide

/- Stored range equality resolves each side by field ID through the direct DateRange owner, and
reports the same class from either authored side. -/
example :
    (match elaborateDirectDateRangeComparison model repeated.id fixed.id .equal with
      | .ok _ => none
      | .error cause => cause.diagnostic?) = some .noWildcard ∧
    (match elaborateDirectDateRangeComparison model fixed.id repeated.id .notEqual with
      | .ok _ => none
      | .error cause => cause.diagnostic?) = some .noWildcard ∧
    (elaborateDirectDateRangeComparison model fixed.id fixed.id .equal).isOk = true := by
  native_decide

/- An exact endpoint selected from a repeatable source reports the class through the direct
owner's own projection, which the bound carriers share. -/
example :
    (match elaborateDateRangeBound model repeated.id .start with
      | .ok _ => none
      | .error cause => cause.diagnostic?) = some .noWildcard ∧
    (elaborateDateRangeBound model fixed.id .start).isOk = true := by
  native_decide

/- A yearless endpoint refuses the operand before it reaches the format and Base-Year gates that
would otherwise refuse this same field, so the locus class is not masked by them. -/
example :
    (match elaborateYearlessDateRangeBound model yearlessRepeated.id .start with
      | .ok _ => none
      | .error cause => cause.diagnostic?) = some .noWildcard ∧
    (match elaborateDateRangeBoundPair model repeated.id .start fixed.id .finish
        .before with
      | .ok _ => none
      | .error cause => cause.diagnostic?) = some .noWildcard := by
  native_decide

/- The reported code is the Kernel's own missing-wildcard class. -/
example : KernelStaticDiagnostic.noWildcard.kernelCode = "MVK_NO_WILDCARD" := by
  decide

end A12Kernel.Conformance.DateRangeRepeatableOperand
