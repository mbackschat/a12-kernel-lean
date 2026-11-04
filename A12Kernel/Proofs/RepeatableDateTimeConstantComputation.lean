import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Elaboration.RepeatableDateTimeConstantComputation

/-! # Repeatable DateTime constant laws -/

namespace A12Kernel

/-- Two checked constants with the same target and the same wall label execute identically however
they are placed: iteration comes from the target's scope and a constant supplies no other source
([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-cross-group-repeatable-constant-target)). -/
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

/-- A label resolvable in the model zone, whose landing the target can evaluate, produces that
evaluation: the target-formatted value of the label its instant lands on, which is the authored label
except across a spring gap or, under UTC, for a Julian leap day. -/
theorem checkedRepeatableDateTimeConstantComputation_outcome_resolvable
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (instant : Instant) (outcome : DateTimeTargetOutcome)
    (resolves :
      operation.dateTimeTarget.profile.resolveStoredLabel? operation.constant = some instant)
    (evaluates : operation.dateTimeTarget.evaluate (.value instant) = .ok outcome) :
    operation.outcome? = some outcome := by
  simp [CheckedRepeatableDateTimeConstantComputation.outcome?, resolves, evaluates, Except.toOption]

/-- A label unresolved in the model zone produces no computed outcome. The execution projection is
locked separately by the carrier's addressed conformance cases. -/
theorem checkedRepeatableDateTimeConstantComputation_outcome_unresolvable
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (unresolved :
      operation.dateTimeTarget.profile.resolveStoredLabel? operation.constant = none) :
    operation.outcome? = none := by
  simp [CheckedRepeatableDateTimeConstantComputation.outcome?, unresolved]

/-- Where an exact instant maps to the constant's own label, the target renders that label and its
stored-text check accepts it, so the carrier stores the authored label. -/
theorem checkedRepeatableDateTimeConstantComputation_renderingAgreesWithResolvedInstant
    {model : FlatModel}
    (operation : CheckedRepeatableDateTimeConstantComputation model)
    (instant : Instant)
    (resolves :
      operation.dateTimeTarget.profile.calendarLabel? instant = some operation.constant)
    (value : Value)
    (readable :
      operation.dateTimeTarget.format.classifyStoredIn operation.dateTimeTarget.profile
        (operation.dateTimeTarget.format.renderParts operation.constant.parts
          operation.constant.time).text = .ok (.parsed value)) :
    operation.dateTimeTarget.evaluate (.value instant) =
      .ok (.accepted
        (operation.dateTimeTarget.format.renderParts operation.constant.parts
          operation.constant.time)) := by
  simp only [CheckedDateTimeFormatTarget.evaluate, resolves, readable]
  rfl

end A12Kernel
