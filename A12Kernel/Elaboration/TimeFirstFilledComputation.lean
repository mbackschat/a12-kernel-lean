import A12Kernel.Elaboration.TemporalFirstFilledShape
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.TimeComputation

/-! # Time `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes over the shared temporal site: a fixed target over a direct
star or a list of plain fields, a repeatable one over a sibling single-axis star at every row of its
scope. Source and target share the whole-second `HH:mm:ss` profile, and the target's clock format
renders the selected clock.
-/

namespace A12Kernel

inductive TimeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledSiteElabError)
  | targetNotTime (path : List String)
  | targetPolicy (cause : TimeTargetElabError)
  deriving Repr, DecidableEq

/-- One `HH:mm:ss` target, fixed or repeatable, and its source of the same bounded carrier. -/
structure CheckedTimeFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledSite model
  time : shape.carrier = .timeHms
  targetPolicy : CheckedClockFormatTarget model

/-- Check the site, the whole-second Time profile, and the target's clock format at its own scope.
Wider formats, policies, nesting, validation use, and materialized-document reconstruction remain
outside. -/
def checkTimeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except TimeFirstFilledComputationElabError (CheckedTimeFirstFilledComputation model) := do
  let shape ← (checkTemporalFirstFilledSite model declaringGroup targetField authored).mapError .shape
  if time : shape.carrier = .timeHms then
    let targetPolicy ← (elaborateClockFormatTargetIn model shape.site.target.repeatableScope
      targetField).mapError .targetPolicy
    pure { shape, time, targetPolicy }
  else throw (.targetNotTime shape.site.target.path)

/-- Project one checked Time cell into the clock-only result consumed by the existing target policy.
Neither stored text nor the runtime transport instant enters this boundary. -/
def timeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : TimeComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.time _ clock)) => .value clock
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present Time or reached formal cause; exhaustion keeps the Time no-value
identity. -/
def evalTimeFirstFilledCells :
    List CheckedAddressedCell → TimeComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match timeFirstFilledCellAt addressed with
      | .noValue => evalTimeFirstFilledCells remaining
      | result => result

/-- One instance's Time selection retained under its exact target address. -/
structure TimeFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : TimeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked Time result backed by the common Time channels over exact cell addresses. -/
structure TimeFirstFilledComputationRunView (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedTimeFirstFilledComputation model
  time : TimeComputationRunView ResidualMessage CellAddr

namespace CheckedTimeFirstFilledComputation

def targetField (operation : CheckedTimeFirstFilledComputation model) : FieldId :=
  operation.shape.site.targetField

def target (operation : CheckedTimeFirstFilledComputation model) : FlatFieldDecl :=
  operation.shape.site.target

def referencesField (operation : CheckedTimeFirstFilledComputation model) : FieldId → Bool :=
  operation.shape.site.referencesField

theorem excludesTarget (operation : CheckedTimeFirstFilledComputation model) :
    operation.referencesField operation.targetField = false :=
  operation.shape.excludesTarget

/-- Scan the source at one target instance's environment, then render the selected clock. -/
def evaluateAt (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) :
    Except FirstFilledSiteFault TimeFirstFilledComputationOutcome := do
  let resolved ← (operation.shape.site.source.resolveAt input read environment).mapError .source
  pure { targetField := target
         outcome := operation.targetPolicy.evaluate (evalTimeFirstFilledCells resolved.cells) }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except FirstFilledSiteFault (List TimeFirstFilledComputationOutcome) :=
  operation.shape.site.instances input .targetRows .targetEnvironment
    (fun target _ => pure { targetField := target, outcome := .noValue })
    (operation.evaluateAt input read)

def execute (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FirstFilledSiteFault (List TimeFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared Time
result owner. -/
def executeResultWithRead (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault (TimeFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure { operation
         time := TimeComputationRunView.fromOutcomesAt input.sourceTimeTargetStateAt residualMessages
           (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

def executeResult (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault (TimeFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedTimeFirstFilledComputation

namespace TimeFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact Time cell-state projections from a separate
checked document of the same model. -/
def applyToChecked (view : TimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (TemporalValueComputationApplicationError CellAddr)
      (TimeComputationDestination CellAddr) :=
  view.time.applyTo destination.sourceTimeTargetStateAt

end TimeFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with Time `FirstFilledValue`. -/
inductive TimeFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : FirstFilledSiteFault)
  deriving Repr, DecidableEq

namespace CheckedTimeFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedTimeFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    (operation.shape.site.source.declarations.map (·.id)) [operation.targetField]

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except TimeFirstFilledCheckedResultFault
      (TimeFirstFilledComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .error cause => .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedTimeFirstFilledComputation

end A12Kernel
