import A12Kernel.Elaboration.TemporalFirstFilledShape
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Full-Date `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes through the shared temporal site, including target-bound
selected scalar and lower-star lists. `FirstFilledPlacement` owns admission and reached-source order. Source and target share one exact full-Date spelling, ISO or dotted, and the target policy
renders and classifies the selected Date.
-/

namespace A12Kernel

inductive FullDateFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledSiteElabError)
  | targetNotFullDate (path : List String)
  | targetPolicy (cause : FullDateTargetElabError)
  deriving Repr, DecidableEq

/-- One full-Date target, fixed or repeatable, and its source sharing one exact spelling. -/
structure CheckedFullDateFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledSite model
  fullDate : shape.carrier = .fullDateIso ∨ shape.carrier = .fullDateDotted
  targetPolicy : CheckedFullDateTarget model

/-- Check the site, the two exact full-Date spellings, and the target's policy at its own scope, which
owns the target's pre-1900 check. The ISO composition is externally measured; dotted target rendering
is measured separately. Wider formats, nesting, validation use, and materialized-document
reconstruction remain outside. -/
def checkFullDateFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except FullDateFirstFilledComputationElabError (CheckedFullDateFirstFilledComputation model) := do
  let shape ← (checkTemporalFirstFilledSite model declaringGroup targetField authored
    (ownsBefore1900 := true)).mapError .shape
  if fullDate : shape.carrier = .fullDateIso ∨ shape.carrier = .fullDateDotted then
    let targetPolicy ← (elaborateFullDateTargetIn model shape.site.target.repeatableScope
      targetField).mapError .targetPolicy
    pure { shape, fullDate, targetPolicy }
  else throw (.targetNotFullDate shape.site.target.path)

/-- Project one checked full-Date cell into the typed root computation result consumed by the target policy. Stored text is deliberately not selected here, so the account does not choose copy over decode/render. -/
def fullDateFirstFilledCellAt
    (addressed : CheckedAddressedCell) : TemporalComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.date date)) => .value date.instant
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present full Date or reached formal cause; exhaustion keeps the temporal no-value identity. -/
def evalFullDateFirstFilledCells :
    List CheckedAddressedCell → TemporalComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match fullDateFirstFilledCellAt addressed with
      | .noValue => evalFullDateFirstFilledCells remaining
      | result => result

/-- A full-Date run's failure: the shared site's, or the target policy's rendering. -/
inductive FullDateFirstFilledComputationFault where
  | site (cause : FirstFilledSiteFault)
  | target (cause : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One instance's full-Date selection retained under its exact target address. -/
structure FullDateFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : FullDateTargetOutcome
  deriving Repr, DecidableEq

/-- One checked full-Date result backed by the common FullDate channels over exact cell addresses. -/
structure FullDateFirstFilledComputationRunView (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedFullDateFirstFilledComputation model
  fullDate : FullDateComputationRunView ResidualMessage CellAddr

namespace CheckedFullDateFirstFilledComputation

def targetField (operation : CheckedFullDateFirstFilledComputation model) : FieldId :=
  operation.shape.site.targetField

def target (operation : CheckedFullDateFirstFilledComputation model) : FlatFieldDecl :=
  operation.shape.site.target

def referencesField (operation : CheckedFullDateFirstFilledComputation model) : FieldId → Bool :=
  operation.shape.site.referencesField

theorem excludesTarget (operation : CheckedFullDateFirstFilledComputation model) :
    operation.referencesField operation.targetField = false :=
  operation.shape.excludesTarget

/-- Scan the source at one target instance's environment, then render the selected Date. -/
def evaluateAt (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) :
    Except FullDateFirstFilledComputationFault FullDateFirstFilledComputationOutcome := do
  let resolved ← (operation.shape.site.source.resolveAt input read environment).mapError
    (.site ∘ .source)
  let outcome ← (operation.targetPolicy.evaluate (evaluateFirstFilledSource resolved .poison (fun resolved => evalFullDateFirstFilledCells resolved.cells))).mapError
    .target
  pure { targetField := target, outcome }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except FullDateFirstFilledComputationFault (List FullDateFirstFilledComputationOutcome) :=
  operation.shape.site.instances input (.site ∘ .targetRows) (.site ∘ .targetEnvironment)
    (fun target _ => pure { targetField := target, outcome := .noValue })
    (operation.evaluateAt input read)

def execute (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FullDateFirstFilledComputationFault (List FullDateFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared FullDate
result owner. -/
def executeResultWithRead (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except FullDateFirstFilledComputationFault
      (FullDateFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure { operation
         fullDate := FullDateComputationRunView.fromOutcomesAt input.sourceFullDateTargetStateAt
           residualMessages
           (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

def executeResult (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except FullDateFirstFilledComputationFault
      (FullDateFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedFullDateFirstFilledComputation

namespace FullDateFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact FullDate cell-state projections from a separate
checked document of the same model. -/
def applyToChecked (view : FullDateFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (FullDateComputationRunView.FullDateComputationRunApplicationError CellAddr)
      (FullDateComputationDestination CellAddr) :=
  view.fullDate.applyTo destination.sourceFullDateTargetStateAt

end FullDateFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with full-Date `FirstFilledValue`. -/
abbrev FullDateFirstFilledCheckedResultFault := ComputationFormalInputRunFault FullDateFirstFilledComputationFault

namespace CheckedFullDateFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedFullDateFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  operation.shape.site.formalInputPlan

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FullDateFirstFilledCheckedResultFault
      (FullDateFirstFilledComputationRunView model ComputationFormalInputFinding) :=
  runWithFormalInputs operation.formalInputPlan input (operation.executeResultWithRead input)

end CheckedFullDateFirstFilledComputation

end A12Kernel
