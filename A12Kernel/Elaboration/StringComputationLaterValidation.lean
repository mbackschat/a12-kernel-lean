import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Elaboration.NumericValidation.Evaluation

/-! # One-level String application followed by Length validation

This bounded SG4 composition applies one retained exact-address String result to a checked destination, enumerates the existing one-level normalized application prefix, and evaluates one checked ordinary direct `Length(String)` comparison at every resulting row. Computed text enters the established validation-phase String normalization before `Length` reads it. The composition does not reconstruct a document, emit rule messages, support other numeric atoms, or define a general later-rule runner.
-/

namespace A12Kernel

inductive StringComputationLaterValidationError where
  | application (cause : StringComputationRepeatableApplicationError)
  | comparisonGroup (expected actual : GroupPath)
  | unsupportedComparison
  | validation (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

private def OrderedNumericValidationAtom.isOrdinaryStringLength :
    OrderedNumericValidationAtom model → Bool
  | .ordinary (.stringLength _) => true
  | _ => false

/-- Whether this bounded later-validation route contains only ordinary direct String-length atoms. Literals remain expression nodes and therefore do not appear in this predicate. -/
def CheckedOrderedNumericComparison.supportsAppliedStringLengthValidation
    (comparison : CheckedOrderedNumericComparison model) : Bool :=
  comparison.core.left.allAtoms
      OrderedNumericValidationAtom.isOrdinaryStringLength &&
    comparison.core.right.allAtoms
      OrderedNumericValidationAtom.isOrdinaryStringLength

private def appliedStringValueCell (value : StoredString) : CheckedCell :=
  formalCheck { kind := .string } (.parsed (.str value.text))

private def appliedStringEmptyCell (present : Bool) : CheckedCell :=
  if present then checkAdmittedRawCell .presentEmpty
  else checkAdmittedRawCell .empty

private def StringComputationRunView.appliedValidationCell
    (view : StringComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedCell := do
  let declaration ←
    (model.lookupUniqueId field).mapError (.field field)
  let path ←
    (environment.pathForScope declaration.repeatableScope)
      |>.mapError .environment
  let address : CellAddr := { field, path }
  match view.withChanges.find? fun computed =>
      computed.targetField == address with
  | some computed => pure (appliedStringValueCell computed.value)
  | none =>
      if view.cleared.contains address then
        pure (appliedStringEmptyCell true)
      else if view.withErrors.any fun computed =>
          computed.targetField == address then
        pure (appliedStringEmptyCell
          (destination.sourceStringTargetStateAt address).isPresent)
      else
        let physical :=
          (repeatableAncestorRowsFor declaration.repeatableScope path).all
            destination.source.instantiatedRows.contains
        if physical then
          destination.read address |>.mapError .document
        else
          pure (appliedStringEmptyCell false)

private def oneLevelStringRowEnvironment
    (level : RepeatableLevel) (row : RowAddr) :
    Except StringComputationLaterValidationError Env :=
  match row.path with
  | [coordinate] => pure [(level, coordinate)]
  | _ => throw .unsupportedComparison

private def evaluateAppliedStringRows
    (view : StringComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (comparison : CheckedOrderedNumericComparison model)
    (level : RepeatableLevel) (rows : List RowAddr) :
    Except StringComputationLaterValidationError (List (Env × Verdict)) :=
  rows.mapM fun row => do
    let environment ← oneLevelStringRowEnvironment level row
    let context : AddressedValidationEvaluationContext model := {
      scalar := {
        fields := destination.flatContext
        groups := GroupPresenceContext.unavailable
      }
      outer := environment
      input := .partialView destination fun current field =>
        (view.appliedValidationCell destination current field).map some
    }
    let verdict ←
      comparison.evalAddressed context |>.mapError .validation
    pure (environment, verdict)

namespace StringComputationRunView

/-- Apply retained String actions, then evaluate one checked direct `Length(String)` comparison at every row of the normalized finite one-level destination prefix. -/
def evaluateOneLevelLengthAfterApplication
    (view : StringComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (level : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model) :
    Except StringComputationLaterValidationError (List (Env × Verdict)) := do
  let applied ←
    (view.applyToCheckedOneLevel destination level)
      |>.mapError .application
  let group ← match model.repeatableGroupAtLevel? level with
    | some group => pure group
    | none => throw .unsupportedComparison
  if comparison.rowGroup != group.path then
    throw (.comparisonGroup group.path comparison.rowGroup)
  if !comparison.supportsAppliedStringLengthValidation then
    throw .unsupportedComparison
  evaluateAppliedStringRows view destination comparison level applied.rows

end StringComputationRunView

end A12Kernel
