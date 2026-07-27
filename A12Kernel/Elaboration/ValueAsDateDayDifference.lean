import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date calendar-day difference

This capsule places one checked partial-Date endpoint on either authored side of the existing concrete-profile `DifferenceInDays` evaluator. It resolves that endpoint once at model-zone midnight, preserves first formal cause and cause-free non-relevance, and delegates every concrete pair to the established exact-label-plus-instant calendar core. Wider Date operands, repeatable addressing, and a general temporal expression tree remain outside.
-/

namespace A12Kernel

/-- One checked zoned partial-Date endpoint and its authored side in a calendar-day difference. -/
structure CheckedValueAsDateDayDifference (model : FlatModel)
    extends CheckedZonedValueAsDateSource model where
  placement : ValueAsDateDifferencePlacement

namespace CheckedValueAsDateDayDifference

/-- Resolve one concrete endpoint at midnight in the model zone. Fresh-label failure remains the existing unsupported-calendar state rather than becoming formal unavailability. -/
private def dayOperand (checked : CheckedValueAsDateDayDifference model) :
    ValueAsDateObservation → CalendarDayDifferenceOperand
  | .empty => .empty
  | .nonRelevant => .unsupportedCalendar
  | .unavailable cause => .unavailable cause
  | .date date =>
      match LocalDateTime.ofDateHms? date 0 0 0 with
      | none => .unsupportedCalendar
      | some localDateTime =>
          match checked.profile.resolveLocal? localDateTime with
          | none => .unsupportedCalendar
          | some instant => .value localDateTime instant

private def evaluateAvailable
    (checked : CheckedValueAsDateDayDifference model)
    (sourceObservation : ValueAsDateObservation)
    (other : CalendarDayDifferenceOperand) :
    Except ValueAsDateDifferenceFault ValueAsDateDifferenceResult :=
  match sourceObservation with
  | .nonRelevant => pure .nonRelevant
  | _ =>
      let sourceOperand := checked.dayOperand sourceObservation
      let evaluated :=
        match checked.placement with
        | .left =>
            CalendarDayDifferenceOperand.evaluate
              checked.profile sourceOperand other
        | .right =>
            CalendarDayDifferenceOperand.evaluate
              checked.profile other sourceOperand
      match evaluated with
      | .ok operand => pure (.operand operand)
      | .error () => throw .unsupportedCalendar

/-- Evaluate both authored reads before helper-level non-relevance or empty substitution, then delegate the concrete case to the existing calendar-day core. -/
def evaluate (checked : CheckedValueAsDateDayDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (other : CalendarDayDifferenceOperand) :
    Except ValueAsDateDifferenceFault ValueAsDateDifferenceResult :=
  let sourceObservation :=
    checked.toCheckedZonedValueAsDateSource.toCheckedValueAsDateSource.observe
      phase cell
  match checked.placement with
  | .left =>
      match sourceObservation with
      | .unavailable cause => pure (.operand (.unknown cause))
      | _ =>
          match other with
          | .unavailable cause => pure (.operand (.unknown cause))
          | _ => checked.evaluateAvailable sourceObservation other
  | .right =>
      match other with
      | .unavailable cause => pure (.operand (.unknown cause))
      | _ =>
          match sourceObservation with
          | .unavailable cause => pure (.operand (.unknown cause))
          | _ => checked.evaluateAvailable sourceObservation other

/-- Check one exact stored-text partial source while preserving an already checked ordinary day-difference operand. -/
def evaluateRaw (checked : CheckedValueAsDateDayDifference model)
    (phase : Phase) (raw : RawCell String)
    (other : CalendarDayDifferenceOperand) :
    Except ValueAsDateDifferenceFault ValueAsDateDifferenceResult :=
  checked.evaluate phase
    (checked.toCheckedZonedValueAsDateSource.toCheckedValueAsDateSource
      |>.checkSourceRaw raw)
    other

end CheckedValueAsDateDayDifference

/-- Resolve one partial-Date endpoint, its model-owned profile, and its authored side in a calendar-day difference. -/
def elaborateValueAsDateDayDifference
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint)
    (placement : ValueAsDateDifferencePlacement) :
    Except ValueAsDateZonedElabError
      (CheckedValueAsDateDayDifference model) := do
  let source ←
    elaborateZonedValueAsDateSource model sourceField endpoint
  pure { source with placement }

end A12Kernel
