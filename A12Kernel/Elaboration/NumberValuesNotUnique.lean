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

namespace CheckedNumberValuesNotUniqueSource

/-- Evaluate the uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and every reached cell reaches the scan, because this operator skips a formally unavailable cell instead of suppressing on it. The result carries firing polarity because a reached filter retypes the message.

Deliberately **not** `resolvedCheckedDocumentValidationAggregateSide`: that resolver converts the first unavailable cell into an operand-level unknown terminal, which is what the aggregates beside this operator need and what this one must not do. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedNumberEntitySource model)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError Verdict := do
  let tagged ← collectTaggedValueListCells
    (fun operand => do
      let resolved ← operand.resolveCheckedValidationOperand document outer
      pure (resolved.valueListSideAt .validation))
    checked.operands
  pure (evalValuesNotUniqueVerdict tagged)

end CheckedNumberValuesNotUniqueSource

end A12Kernel
