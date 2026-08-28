import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Elaboration.NumericValidation.Evaluation

/-! # Bounded Number application followed by numeric validation

This bounded SG4 composition applies one retained exact-address Number result to a checked destination, enumerates either the existing one-level normalized application prefix or the concrete inner rows of the existing two-level parent-scoped topology, and evaluates one checked ordinary direct-Number comparison at every selected row. The validation reader overlays retained actions on the destination while preserving unrelated checked cells. It does not reconstruct a document, emit rule messages, support specialized numeric atoms, or define a general later-rule runner.
-/

namespace A12Kernel

inductive NumericComputationLaterValidationError where
  | application (cause : NumericComputationDocumentApplicationError)
  | comparisonGroup (expected actual : GroupPath)
  | unsupportedComparison
  | validation (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

private def OrderedNumericValidationAtom.isOrdinaryDirectNumber :
    OrderedNumericValidationAtom model → Bool
  | .ordinary (.field _) => true
  | _ => false

/-- Whether this bounded later-validation route contains only ordinary direct Number atoms. Literals remain expression nodes and therefore do not appear in this predicate. -/
def CheckedOrderedNumericComparison.supportsAppliedNumberValidation
    (comparison : CheckedOrderedNumericComparison model) : Bool :=
  comparison.core.left.allAtoms
      OrderedNumericValidationAtom.isOrdinaryDirectNumber &&
    comparison.core.right.allAtoms
      OrderedNumericValidationAtom.isOrdinaryDirectNumber

private def appliedValueCell (value : StoredNumber) : CheckedCell :=
  checkAdmittedRawCell (.parsed (.num value.amount))

private def appliedEmptyCell (present : Bool) : CheckedCell :=
  if present then checkAdmittedRawCell .presentEmpty
  else checkAdmittedRawCell .empty

private def NumericComputationRunView.appliedValidationCell
    (view : NumericComputationRunView Message CellAddr)
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
  | some computed => pure (appliedValueCell computed.value)
  | none =>
      if view.cleared.contains address then
        pure (appliedEmptyCell true)
      else if view.withErrors.any fun computed =>
          computed.targetField == address then
        pure (appliedEmptyCell
          (destination.numericTargetPlacementStateAt address).isPresent)
      else
        let physical :=
          (repeatableAncestorRowsFor declaration.repeatableScope path).all
            destination.source.instantiatedRows.contains
        if physical then
          destination.read address |>.mapError .document
        else
          pure (appliedEmptyCell false)

private def rowEnvironment (level : RepeatableLevel) (row : RowAddr) :
    Except NumericComputationLaterValidationError Env :=
  match row.path with
  | [coordinate] => pure [(level, coordinate)]
  | _ => throw .unsupportedComparison

private def evaluateAppliedEnvironments
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (comparison : CheckedOrderedNumericComparison model)
    (environments : List Env) :
    Except NumericComputationLaterValidationError (List (Env × Verdict)) :=
  environments.mapM fun environment => do
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

private def evaluateAppliedRows
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (comparison : CheckedOrderedNumericComparison model)
    (level : RepeatableLevel) (rows : List RowAddr) :
    Except NumericComputationLaterValidationError (List (Env × Verdict)) := do
  let environments ← rows.mapM (rowEnvironment level)
  evaluateAppliedEnvironments view destination comparison environments

private def twoLevelRowEnvironment
    (outer inner : RepeatableLevel) (row : RowAddr) :
    Except NumericComputationLaterValidationError Env :=
  match row.path with
  | [outerCoordinate, innerCoordinate] =>
      pure [(outer, outerCoordinate), (inner, innerCoordinate)]
  | _ => throw .unsupportedComparison

private def evaluateAppliedTwoLevelRows
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (comparison : CheckedOrderedNumericComparison model)
    (outer inner : RepeatableLevel) (rows : List RowAddr) :
    Except NumericComputationLaterValidationError (List (Env × Verdict)) := do
  let environments ← rows.mapM (twoLevelRowEnvironment outer inner)
  evaluateAppliedEnvironments view destination comparison environments

namespace NumericComputationRunView

/-- Apply retained Number actions, then evaluate one checked direct-Number comparison at every row of the normalized finite one-level destination prefix. Application remains source-relative and validation reads the applied destination explicitly. -/
def evaluateOneLevelAfterApplication
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model) (level : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model) :
    Except NumericComputationLaterValidationError (List (Env × Verdict)) := do
  let applied ←
    (view.applyToCheckedOneLevel destination level)
      |>.mapError .application
  let group ← match model.repeatableGroupAtLevel? level with
    | some group => pure group
    | none => throw .unsupportedComparison
  if comparison.rowGroup != group.path then
    throw (.comparisonGroup group.path comparison.rowGroup)
  if !comparison.supportsAppliedNumberValidation then
    throw .unsupportedComparison
  evaluateAppliedRows view destination comparison level applied.rows

/-- Apply retained Number actions, then evaluate one checked direct-Number comparison at every concrete inner row in the normalized finite two-level destination topology. A padded outer predecessor without an inner row does not create a validation environment. -/
def evaluateTwoLevelAfterApplication
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel)
    (comparison : CheckedOrderedNumericComparison model) :
    Except NumericComputationLaterValidationError (List (Env × Verdict)) := do
  let applied ←
    (view.applyToCheckedTwoLevel destination outer inner)
      |>.mapError .application
  let group ← match model.repeatableGroupAtLevel? inner with
    | some group => pure group
    | none => throw .unsupportedComparison
  if comparison.rowGroup != group.path then
    throw (.comparisonGroup group.path comparison.rowGroup)
  if !comparison.supportsAppliedNumberValidation then
    throw .unsupportedComparison
  evaluateAppliedTwoLevelRows view destination comparison
    outer inner applied.leafRows

end NumericComputationRunView

end A12Kernel
