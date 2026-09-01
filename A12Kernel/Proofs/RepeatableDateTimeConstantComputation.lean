import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Elaboration.RepeatableDateTimeConstantComputation

/-! # Repeatable DateTime constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same wall label execute identically however
they are placed: iteration comes from the target's scope and a constant supplies no other source
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/
theorem checkedRepeatableDateTimeConstantComputation_execute_ignoresDeclaringGroup
    {model : FlatModel}
    (first second : CheckedRepeatableDateTimeConstantComputation model)
    (sameTarget :
      first.checkedTarget.targetField = second.checkedTarget.targetField)
    (sameDeclaration :
      first.checkedTarget.declaration = second.checkedTarget.declaration)
    (sameDateTimeTarget : first.dateTimeTarget = second.dateTimeTarget)
    (sameConstant : first.constant = second.constant)
    (input : CheckedDocument model) :
    first.execute input = second.execute input := by
  simp only [CheckedRepeatableDateTimeConstantComputation.execute,
    CheckedRepeatableDateTimeConstantComputation.outcome?,
    sameTarget, sameDeclaration, sameDateTimeTarget, sameConstant]

/-- A label resolvable in the model zone produces the target-formatted accepted value. The resolved
instant is used only as an admission witness; storage retains the authored local components. -/
theorem checkedRepeatableDateTimeConstantComputation_outcome_resolvable
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (instant : Instant)
    (resolves :
      operation.dateTimeTarget.profile.resolveLocal? operation.constant = some instant) :
    operation.outcome? =
      some (.accepted
        (DateTimeTargetFormat.render operation.dateTimeTarget.format operation.constant)) := by
  simp [CheckedRepeatableDateTimeConstantComputation.outcome?, resolves]

/-- A label unresolved in the model zone produces no computed outcome. The execution projection is
locked separately by the carrier's addressed conformance cases. -/
theorem checkedRepeatableDateTimeConstantComputation_outcome_unresolvable
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (unresolved :
      operation.dateTimeTarget.profile.resolveLocal? operation.constant = none) :
    operation.outcome? = none := by
  simp [CheckedRepeatableDateTimeConstantComputation.outcome?, unresolved]

/-- Where an exact instant maps to the constant's local label, both routes use the same renderer. -/
theorem checkedRepeatableDateTimeConstantComputation_renderingAgreesWithResolvedInstant
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (instant : Instant)
    (resolves :
      operation.dateTimeTarget.profile.localDateTime? instant = some operation.constant) :
    operation.dateTimeTarget.evaluate (.value instant) =
      .ok (.accepted
        (DateTimeTargetFormat.render operation.dateTimeTarget.format operation.constant)) := by
  simp only [CheckedDateTimeTarget.evaluate,
    resolves]
  rfl

end A12Kernel
