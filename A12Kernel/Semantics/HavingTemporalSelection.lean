import A12Kernel.Semantics.HavingFirstFilled
import A12Kernel.Semantics.ScalarTemporalValue
import A12Kernel.Semantics.FullDateInputFormat

namespace A12Kernel

inductive HavingTemporalSelection where
  | firstFilled
  | extremum (operator : TemporalExtremumOp)
  deriving Repr, DecidableEq

/-- Only selection admits partial-Date cells; direct temporal expression reads keep their own gate. -/
structure HavingTemporalSelectionRef extends HavingTemporalRef where
  partialFormat : Option FullDateTargetFormat := none
  deriving Repr, DecidableEq

namespace HavingTemporalSelectionRef

/-- Selection completes a checked partial value to its earliest date and preserves unknown-year
non-relevance (spec/05; SOURCES.md#inbound-2026-10-02-partial-date-readers). -/
def project (reference : HavingTemporalSelectionRef) (baseYear : Option Int)
    (profile : ModelZone.ConcreteProfile) (observation : CellObservation) :
    SimpleComparisonOperand ScalarTemporalValue :=
  match observation with
  | .value (.partialDate text) =>
      match reference.partialFormat.bind (·.parseComponents? text) with
      | none => .unknown .malformed
      | some parts =>
          if parts.year == 0 then .value .nonRelevant true
          else match profile.resolveCompletedDateParts? {
              parts with month := max 1 parts.month, day := max 1 parts.day } with
            | some value => .value (.date value) true
            | none => .unknown .malformed
  | _ => projectScalarTemporalObservationWith baseYear (some profile) reference.field observation

end HavingTemporalSelectionRef

namespace HavingTemporalSelection

def presenceSlots (slots : List (HavingFieldListSlot HavingTemporalSelectionRef)) :
    List (HavingFieldListSlot HavingPresenceRef) :=
  slots.map (·.map fun reference => { origin := reference.origin, field := reference.field.id })

/-- Both selectors retain declared precision and use the ordinary temporal projection (spec/07 §5).
First-filled stops at the selected payload; extrema retain missing tails and computation poison. -/
def evaluate (selection : HavingTemporalSelection) (baseYear : Option Int)
    (profile : ModelZone.ConcreteProfile) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot HavingTemporalSelectionRef)) :
    Except Error (SimpleComparisonOperand ScalarTemporalValue) := do
  let project (reference : HavingTemporalSelectionRef) (cell : CheckedCell) :=
    reference.project baseYear profile (observeCell phase cell)
  match selection with
  | .firstFilled =>
      let result ← HavingFirstFilled.scanWith (·.origin) (·.field.id)
        (fun state reference cell =>
          let observation := match project reference cell with
            | .notEvaluated => CellObservation.empty
            | .unknown cause => .unknown cause
            | .value value _ => .value value
          scanFirstFilledObservations [observation] state) context frame slots
      pure (match result with | .inl _ => .notEvaluated | .inr value => value)
  | .extremum operator =>
      let result ← HavingFieldListSlot.foldRead (·.origin) (·.field.id) context frame
        (fun (values, tail) reference environment => do
          let value := project reference (← context.read environment reference.field.id)
          if phase == .computation then
            if let .unknown cause := value then return .inr (.unknown cause)
          pure (.inl (value :: values, tail))) ([], false) slots
        (fun (values, _) _ => pure (.inl (values, true)))
      pure (match result with
        | .inr value => value
        | .inl (values, tail) => evalTemporalExtremumAggregate (ScalarTemporalValue.select operator)
            { operands := values.reverse, hasUninstantiatedTail := tail, hasHaving := false })

end HavingTemporalSelection
end A12Kernel
