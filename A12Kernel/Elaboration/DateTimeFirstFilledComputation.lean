import A12Kernel.Elaboration.TemporalFirstFilledShape
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # DateTime `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes over the shared temporal site: a fixed target over a direct
star or a list of plain fields, a repeatable one over a sibling single-axis star at every row of its
scope. Source and target share the ISO whole-second profile, and the target renders the selected exact
instant in the model zone.
-/

namespace A12Kernel

inductive DateTimeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledSiteElabError)
  | targetNotDateTime (path : List String)
  | targetPolicy (cause : DateTimeTargetElabError)
  deriving Repr, DecidableEq

/-- One ISO whole-second DateTime target, fixed or repeatable, and its source of the same carrier. -/
structure CheckedDateTimeFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledSite model
  dateTime : shape.carrier = .dateTimeIso
  targetPolicy : CheckedDateTimeTarget model

/-- Check the site, the ISO whole-second DateTime profile, and the target's policy at its own scope.
Alternate formats, nesting, validation use, and materialized-document reconstruction remain
outside. -/
def checkDateTimeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except DateTimeFirstFilledComputationElabError (CheckedDateTimeFirstFilledComputation model) := do
  let shape ← (checkTemporalFirstFilledSite model declaringGroup targetField authored).mapError .shape
  if dateTime : shape.carrier = .dateTimeIso then
    let targetPolicy ← (elaborateDateTimeTargetIn model shape.site.target.repeatableScope
      targetField).mapError .targetPolicy
    pure { shape, dateTime, targetPolicy }
  else throw (.targetNotDateTime shape.site.target.path)

/-- Project one checked DateTime cell to its exact instant before model-zone target rendering. -/
def dateTimeFirstFilledCellAt (addressed : CheckedAddressedCell) : TemporalComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.dateTime instant _ _ _)) => .value instant
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present exact instant or reached formal cause; exhaustion keeps the temporal no-value identity. -/
def evalDateTimeFirstFilledCells : List CheckedAddressedCell → TemporalComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match dateTimeFirstFilledCellAt addressed with
      | .noValue => evalDateTimeFirstFilledCells remaining
      | result => result

/-- A DateTime run's failure: the shared site's, or the target policy's rendering. -/
inductive DateTimeFirstFilledComputationFault where
  | site (cause : FirstFilledSiteFault)
  | target (cause : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One instance's DateTime selection retained under its exact target address. -/
structure DateTimeFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : DateTimeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked DateTime result backed by the common DateTime channels over exact cell addresses. -/
structure DateTimeFirstFilledComputationRunView (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedDateTimeFirstFilledComputation model
  dateTime : DateTimeComputationRunView ResidualMessage CellAddr

namespace CheckedDateTimeFirstFilledComputation

def targetField (operation : CheckedDateTimeFirstFilledComputation model) : FieldId :=
  operation.shape.site.targetField

def target (operation : CheckedDateTimeFirstFilledComputation model) : FlatFieldDecl :=
  operation.shape.site.target

def referencesField (operation : CheckedDateTimeFirstFilledComputation model) : FieldId → Bool :=
  operation.shape.site.referencesField

theorem excludesTarget (operation : CheckedDateTimeFirstFilledComputation model) :
    operation.referencesField operation.targetField = false :=
  operation.shape.excludesTarget

/-- Scan the source at one target instance's environment, then render the selected instant. -/
def evaluateAt (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) :
    Except DateTimeFirstFilledComputationFault DateTimeFirstFilledComputationOutcome := do
  let resolved ← (operation.shape.site.source.resolveAt input read environment).mapError
    (.site ∘ .source)
  let outcome ← (operation.targetPolicy.evaluate (evalDateTimeFirstFilledCells resolved.cells)).mapError
    .target
  pure { targetField := target, outcome }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except DateTimeFirstFilledComputationFault (List DateTimeFirstFilledComputationOutcome) :=
  operation.shape.site.instances input (.site ∘ .targetRows) (.site ∘ .targetEnvironment)
    (fun target _ => pure { targetField := target, outcome := .noValue })
    (operation.evaluateAt input read)

def execute (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateTimeFirstFilledComputationFault (List DateTimeFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared DateTime
result owner. -/
def executeResultWithRead (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except DateTimeFirstFilledComputationFault
      (DateTimeFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure { operation
         dateTime := DateTimeComputationRunView.fromOutcomesAt input.sourceDateTimeTargetStateAt
           residualMessages
           (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

def executeResult (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except DateTimeFirstFilledComputationFault
      (DateTimeFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedDateTimeFirstFilledComputation

namespace DateTimeFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact DateTime cell-state projections from a separate
checked document of the same model. -/
def applyToChecked (view : DateTimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (DateTimeComputationRunView.DateTimeComputationRunApplicationError CellAddr)
      (DateTimeComputationDestination CellAddr) :=
  view.dateTime.applyTo destination.sourceDateTimeTargetStateAt

end DateTimeFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with DateTime `FirstFilledValue`. -/
inductive DateTimeFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : DateTimeFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedDateTimeFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedDateTimeFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    (operation.shape.site.source.declarations.map (·.id)) [operation.targetField]

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateTimeFirstFilledCheckedResultFault
      (DateTimeFirstFilledComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .error cause => .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedDateTimeFirstFilledComputation

end A12Kernel
