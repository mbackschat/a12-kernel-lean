import A12Kernel.Elaboration.NumericAggregate.Entities

/-! # Checked Number `FieldValuesNotUnique`

This consumer applies the common checked Number entity list to `FieldValuesNotUnique`. It owns only the uniqueness verdict; slot admission, authored order, repeated-direct-field rejection, the multiple-slots-or-one-star rule, and Number-valued certification stay in `NumberEntityList`, and the membership boundary stays with the shared distinct scan.

Real-kernel authoring admits the plain field list over two or three Number fields of differing declared scales, the starred single-field form, and a mixed direct-plus-starred list; it rejects a single direct operand and a list mixing Number with another kind. The String/stored-Enumeration and date-like overloads of the same operator are deliberately not admitted here.
-/

namespace A12Kernel

abbrev SurfaceNumberValuesNotUniqueOperand := SurfaceNumberEntityOperand
abbrev SurfaceNumberValuesNotUniqueSource := SurfaceNumberEntitySource
abbrev CheckedNumberValuesNotUniqueSource := CheckedNumberEntitySource
abbrev NumberValuesNotUniqueElabError := NumberEntityElabError

/-- Admit one `FieldValuesNotUnique` operand list through the shared Number entity-list contract. -/
def elaborateNumberValuesNotUniqueSource := @elaborateNumberEntitySource

private def emptySide : ResolvedValueListSide .number :=
  { cells := [], hasUninstantiatedTail := false, hasHaving := false }

namespace CheckedNumberValuesNotUniqueSource

/-- Evaluate the uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and the first formally unavailable reached cell stops the scan, so no later star topology or filter is sampled. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedNumberEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError K := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide .number) (terminal := K)
      (fun operand => do
        -- The shared resolver's early terminal is always an operand-level formal
        -- unavailability, which this predicate reports as UNKNOWN.
        match ← operand.resolvedCheckedDocumentValidationAggregateSide
            document outer with
        | .inl side => pure (.inl side)
        | .inr _ => pure (.inr K.unknown))
      (fun _cause => K.unknown)
      (fun accumulated _ side => accumulated.append side)
      checked.operands emptySide with
  | .inl side => pure (evalValuesNotUnique side.cells)
  | .inr verdict => pure verdict

end CheckedNumberValuesNotUniqueSource

end A12Kernel
