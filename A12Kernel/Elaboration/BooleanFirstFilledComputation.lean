import A12Kernel.Elaboration.FirstFilledPlacement
import A12Kernel.Elaboration.BooleanComputationResult
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Semantics.FirstFilledValue

/-! # Boolean `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes over the shared first-filled site, and specializes the shared
target-polymorphic typed result/application fold over exact cell addresses.
-/

namespace A12Kernel

inductive BooleanFirstFilledComputationElabError where
  | site (cause : FirstFilledPlacementElabError)
  | targetKind (path : List String) (actual : SurfaceScalarKind)
  | sourceKind (path : List String) (actual : SurfaceScalarKind)
  /-- A list source naming the target itself. -/
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

/-- One Boolean target, fixed or repeatable, and one Boolean source placed on the shared site. -/
structure CheckedBooleanFirstFilledComputation (model : FlatModel) where
  private mk ::
  site : CheckedFirstFilledSite model
  targetBoolean : site.target.policy.kind = .boolean
  sourceBoolean : site.source.declarations.all (·.policy.kind == .boolean) = true
  excludesTarget : site.referencesField site.targetField = false

/-- Check the externally measured Boolean computation shapes: a direct single-level star or a direct
list at a fixed target, a sibling star at a repeatable one. Wider `entitySpec`, nested repetition and
validation use remain outside this boundary. -/
def checkBooleanFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except BooleanFirstFilledComputationElabError
      (CheckedBooleanFirstFilledComputation model) := do
  -- The target's kind is checked before its placement, so a non-Boolean target is refused as such
  -- wherever it sits.
  if let .ok target := model.lookupUniqueId targetField then
    if target.policy.kind != .boolean then
      throw (.targetKind target.path target.policy.kind.surfaceKind)
  let site ← (checkFirstFilledSite model declaringGroup targetField authored).mapError .site
  if hTargetKind : site.target.policy.kind = .boolean then
    if hSourceKind : site.source.declarations.all (·.policy.kind == .boolean) = true then
      if hExcludes : site.referencesField site.targetField = false then
        pure { site, targetBoolean := hTargetKind, sourceBoolean := hSourceKind
               excludesTarget := hExcludes }
      else throw (.targetSelfReference site.target.path)
    else
      let other := (site.source.declarations.find? (·.policy.kind != .boolean)).getD site.target
      throw (.sourceKind other.path other.policy.kind.surfaceKind)
  else throw (.targetKind site.target.path site.target.policy.kind.surfaceKind)

/-- Classify one checked Boolean source cell for computation-phase first-filled selection. -/
def booleanFirstFilledCellAt (cell : CheckedCell) : FirstFilledBooleanCell :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.bool value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- One instance's Boolean selection retained under its exact target address. -/
structure BooleanFirstFilledComputationOutcome where
  targetField : CellAddr
  result : FirstFilledBooleanComputationResult
  deriving Repr, DecidableEq

/-- Five extensional result collections for one model-certified Boolean `FirstFilledValue`
computation over exact cell addresses. Retaining the checked operation makes every possible action
target-owned. -/
structure BooleanFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedBooleanFirstFilledComputation model
  boolean : BooleanComputationRunView ResidualMessage CellAddr

namespace BooleanFirstFilledComputationRunView

def withoutErrors (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.withoutErrors

def withChanges (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.withChanges

def withErrors (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.withErrors

def cleared (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.cleared

def formalErrorsInOperands
    (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.formalErrorsInOperands

/-- The result's public error predicate delegates to the shared typed channels. -/
def noErrorOccurred
    (view : BooleanFirstFilledComputationRunView model ResidualMessage) : Bool :=
  view.boolean.noErrorOccurred

/-- Targets consumed by the retained Boolean actions. -/
def actionTargets
    (view : BooleanFirstFilledComputationRunView model ResidualMessage) :
    List CellAddr :=
  view.boolean.actionTargets

/-- Apply source-classified Boolean actions to a separately supplied checked document of the same
certified model. Unchanged successes and residual messages are inert. -/
def applyToChecked
    (view : BooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) : BooleanComputationDestination CellAddr :=
  view.boolean.applyTo destination.sourceBooleanTargetStateAt

end BooleanFirstFilledComputationRunView

namespace CheckedBooleanFirstFilledComputation

def targetField (operation : CheckedBooleanFirstFilledComputation model) : FieldId :=
  operation.site.targetField

def target (operation : CheckedBooleanFirstFilledComputation model) : FlatFieldDecl :=
  operation.site.target

def referencesField (operation : CheckedBooleanFirstFilledComputation model) : FieldId → Bool :=
  operation.site.referencesField

/-- Scan the source at one target instance's environment. Structural addressing failure stays outside
the semantic no-value/poison result. -/
def evaluateAt (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) :
    Except FirstFilledSiteFault BooleanFirstFilledComputationOutcome := do
  let resolved ← (operation.site.source.resolveAt input read environment).mapError .source
  pure { targetField := target
         result := evalFirstFilledBoolean
           (resolved.cells.map fun cell => booleanFirstFilledCellAt cell.cell) }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except FirstFilledSiteFault (List BooleanFirstFilledComputationOutcome) :=
  operation.site.instances input .targetRows .targetEnvironment
    (fun target _ => pure { targetField := target, result := .noValue })
    (operation.evaluateAt input read)

def execute (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FirstFilledSiteFault (List BooleanFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared Boolean
result owner. Exhaustion and reached poison clear only a source-filled target. -/
def executeResultWithRead (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault (BooleanFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure { operation
         boolean := BooleanComputationRunView.fromSourcedOutcomes residualMessages
           (outcomes.map fun entry =>
             (entry.targetField, entry.result, input.sourceBooleanTargetStateAt entry.targetField)) }

def executeResult (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault (BooleanFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedBooleanFirstFilledComputation

/-- Failure while composing selected formal-input preparation with Boolean `FirstFilledValue`. -/
inductive BooleanFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : FirstFilledSiteFault)
  deriving Repr, DecidableEq

namespace CheckedBooleanFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedBooleanFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    (operation.site.source.declarations.map (·.id)) [operation.targetField]

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except BooleanFirstFilledCheckedResultFault
      (BooleanFirstFilledComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .error cause => .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedBooleanFirstFilledComputation

end A12Kernel
