import A12Kernel.Elaboration.StringComputationRun
import A12Kernel.Semantics.StringApplication

/-! # String-specific V2 computation result projection

This capsule projects a successful checked nonrepeatable String run against the immutable source document. It preserves successful unchanged values, the source-relative changed subset, payloadful target errors, source-filled clearing, and the independently supplied residual message channel exposed by the V2 API as `formalErrorsInOperands`. Residual-message construction, eager formal checking, message rendering, application, other target families, and repeatable pointers remain separate.
-/

namespace A12Kernel

/-- One successful non-clearing computed String instance. -/
structure StringComputedInstance where
  targetField : FieldId
  value : StoredString
  deriving Repr, DecidableEq

/-- One computed String instance whose attempted stored value failed target checking. -/
structure StringComputedError where
  targetField : FieldId
  attempted : StoredString
  cause : StringTargetError
  deriving Repr, DecidableEq

namespace StringTargetOutcome

/-- Whether the runtime produced a nonempty computed-data instance. Target-rejected attempts count; clean no-value and inherited poison do not. -/
def hasComputedInstance : StringTargetOutcome → Bool
  | .accepted _ | .errored _ _ => true
  | .noValue | .poison _ => false

end StringTargetOutcome

namespace CheckedDocument

/-- Recover the exact source placement and stored text for one nonrepeatable String target. Target-policy validity is irrelevant to source-relative change and clearing classification. -/
def sourceStringTargetState (input : CheckedDocument model)
    (field : FieldId) : StringTargetState :=
  match input.source.cells.find? fun cell =>
      cell.address == ({ field, path := [] } : CellAddr) with
  | none => .absent
  | some cell =>
      if empty : cell.stored = "" then
        .presentEmpty
      else
        .presentValue { text := cell.stored, nonempty := empty }

end CheckedDocument

/-- The String fragment of the immutable V2 result. The residual payload remains opaque so its later partition/message owner can be threaded without a second message representation. Lists represent extensional collections; their order is not public. -/
structure StringComputationRunView (ResidualMessage : Type) where
  private mk ::
  withoutErrors : List StringComputedInstance
  withChanges : List StringComputedInstance
  withErrors : List StringComputedError
  cleared : List FieldId
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

namespace StringComputationRunView

/-- Project the successful computed instance, retaining unchanged values. -/
def successfulInstance? :
    FieldId × StringTargetOutcome → Option StringComputedInstance
  | (targetField, .accepted value) => some { targetField, value }
  | _ => none

/-- Project only payloadful target rejection. Inherited poison carries no computed-instance message. -/
def computedError? :
    FieldId × StringTargetOutcome → Option StringComputedError
  | (targetField, .errored attempted cause) =>
      some { targetField, attempted, cause }
  | _ => none

/-- Compare a successful String value with the immutable computation source, not a later application destination. -/
def sourceValueChanged (input : CheckedDocument model)
    (computed : StringComputedInstance) : Bool :=
  (input.sourceStringTargetState computed.targetField).storedValue !=
    some computed.value

/-- A source-filled target is publicly cleared exactly when execution produced no computed-data instance. A target-rejected attempt therefore belongs only to `withErrors`, even though later application clears it. -/
def shouldClear (input : CheckedDocument model)
    (entry : FieldId × StringTargetOutcome) : Bool :=
  !entry.2.hasComputedInstance &&
    (input.sourceStringTargetState entry.1).storedValue.isSome

/-- Build the extensional String result from rich run outcomes. The separately supplied residual messages are retained unchanged; this function does not claim how pointer partitioning or eager formal checking constructs them. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × StringTargetOutcome)) :
    StringComputationRunView ResidualMessage :=
  let withoutErrors := outcomes.filterMap successfulInstance?
  {
    withoutErrors
    withChanges := withoutErrors.filter (sourceValueChanged input)
    withErrors := outcomes.filterMap computedError?
    cleared := (outcomes.filter (shouldClear input)).map Prod.fst
    formalErrorsInOperands := residualMessages
  }

/-- The V2 error predicate observes exactly the computed-instance and residual message channels. Changes and clearing are not errors. -/
def noErrorOccurred (view : StringComputationRunView ResidualMessage) : Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

/-- Order-independent equality of the five V2 collections. The private plan order remains an execution fact, not a public result-order guarantee. -/
def ExtensionalEq (left right : StringComputationRunView ResidualMessage) : Prop :=
  left.withoutErrors.Perm right.withoutErrors ∧
    left.withChanges.Perm right.withChanges ∧
    left.withErrors.Perm right.withErrors ∧
    left.cleared.Perm right.cleared ∧
    left.formalErrorsInOperands.Perm right.formalErrorsInOperands

end StringComputationRunView

namespace CheckedStringComputationRun

/-- Execute the checked run and classify its rich outcomes relative to that same immutable source document. -/
def executeResult (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except StringComputationRunFault (StringComputationRunView ResidualMessage) := do
  let outcomes ← run.execute patterns input
  pure (StringComputationRunView.fromOutcomes input residualMessages outcomes)

end CheckedStringComputationRun

end A12Kernel
