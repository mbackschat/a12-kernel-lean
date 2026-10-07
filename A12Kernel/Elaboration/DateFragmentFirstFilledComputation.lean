import A12Kernel.Elaboration.TemporalFirstFilledShape
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # DateFragment `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes through the shared temporal site, including target-bound
selected scalar and lower-star lists. `FirstFilledPlacement` owns admission and reached-source order. Target and source share one of the four exact fragment profiles, and the selected stored token
is written as it stands.
-/

namespace A12Kernel

inductive DateFragmentFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledSiteElabError)
  | targetNotFragment (path : List String)
  deriving Repr, DecidableEq

/-- One DateFragment target, fixed or repeatable, and its source sharing one exact fragment profile. -/
structure CheckedDateFragmentFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledSite model
  fragment : shape.carrier.isDateFragment = true

/-- Check the site and the four exact admitted DateFragment profiles. Runtime calibration covers the
`MM` star and the `yyyy-MM` direct list at a fixed target. -/
def checkDateFragmentFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except DateFragmentFirstFilledComputationElabError
      (CheckedDateFragmentFirstFilledComputation model) := do
  let shape ← (checkTemporalFirstFilledSite model declaringGroup targetField authored).mapError .shape
  if fragment : shape.carrier.isDateFragment = true then pure { shape, fragment }
  else throw (.targetNotFragment shape.site.target.path)

/-- Project one checked DateFragment cell to the token consumed by the shared first-filled scan. Only
the `MM` runtime row is externally calibrated, and it does not distinguish copy from render. -/
def dateFragmentFirstFilledCellAt
    (addressed : CheckedAddressedCell) : ValueListCell .token :=
  match observeCell .computation addressed.cell, addressed.stored with
  | .value (.temporal (.date _)), some token => .present token
  | .value _, _ => .unknown .malformed
  | .empty, _ => .empty
  | .unknown cause, _ | .poison cause, _ => .unknown cause

/-- One checked DateFragment `FirstFilledValue` result backed by the common exact-text channels. -/
structure DateFragmentFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedDateFragmentFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedDateFragmentFirstFilledComputation

def targetField (operation : CheckedDateFragmentFirstFilledComputation model) : FieldId :=
  operation.shape.site.targetField

def target (operation : CheckedDateFragmentFirstFilledComputation model) : FlatFieldDecl :=
  operation.shape.site.target

def referencesField (operation : CheckedDateFragmentFirstFilledComputation model) :
    FieldId → Bool :=
  operation.shape.site.referencesField

theorem excludesTarget (operation : CheckedDateFragmentFirstFilledComputation model) :
    operation.referencesField operation.targetField = false :=
  operation.shape.excludesTarget

/-- Evaluate the shared checked DateFragment token scan over cells resolved at one instance. -/
def evalResolvedDateFragmentFirstFilled
    (cells : List CheckedAddressedCell) (hasOpenTail : Bool) : TokenComputationResult :=
  let side : ResolvedValueListSide .token := {
    cells := cells.map dateFragmentFirstFilledCellAt
    hasUninstantiatedTail := hasOpenTail
    hasHaving := false
  }
  (evalFirstFilledToken side).asComputationResult

/-- Scan the source at one target instance's environment through a caller-supplied view. -/
def evaluateAt (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) :
    Except FirstFilledSiteFault AddressedTokenComputationOutcome := do
  let resolved ← (operation.shape.site.source.resolveAt input read environment).mapError .source
  pure { targetField := target
         result := evaluateFirstFilledSource resolved .poison (fun resolved =>
           evalResolvedDateFragmentFirstFilled resolved.cells resolved.hasOpenTail) }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except FirstFilledSiteFault (List AddressedTokenComputationOutcome) :=
  operation.shape.site.instances input .targetRows .targetEnvironment
    (fun target _ => pure { targetField := target, result := .noValue })
    (operation.evaluateAt input read)

def execute (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FirstFilledSiteFault (List AddressedTokenComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view token outcomes against the immutable source target at the same addresses.
This result boundary does not claim that the Kernel copies rather than rerenders the fragment. -/
def executeResultWithRead (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault
      (DateFragmentFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure { operation, string := projectAddressedTokenResults input residualMessages outcomes }

def executeResult (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault
      (DateFragmentFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedDateFragmentFirstFilledComputation

namespace DateFragmentFirstFilledComputationRunView

/-- Apply retained exact-address fragment actions to a separate same-model destination. The result
is a text-state projection, not a reconstructed document or implicit validation pass. -/
def applyToChecked
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end DateFragmentFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with DateFragment `FirstFilledValue`. -/
abbrev DateFragmentFirstFilledCheckedResultFault := ComputationFormalInputRunFault FirstFilledSiteFault

namespace CheckedDateFragmentFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedDateFragmentFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  operation.shape.site.formalInputPlan

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateFragmentFirstFilledCheckedResultFault
      (DateFragmentFirstFilledComputationRunView model ComputationFormalInputFinding) :=
  runWithFormalInputs operation.formalInputPlan input (operation.executeResultWithRead input)

end CheckedDateFragmentFirstFilledComputation

end A12Kernel
