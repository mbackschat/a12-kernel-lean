import A12Kernel.Elaboration.TemporalFirstFilledShape
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Elaboration.DateConstantTarget
import A12Kernel.Semantics.FirstFilledDate

/-! # Date `FirstFilledValue` at a fixed or a repeatable target

One carrier serves complete and component-omitting Date targets through the shared temporal site,
including target-bound selected entity lists. `FirstFilledPlacement` owns admission and reached-source
order. A source list retains one exact profile; the independent target policy renders and classifies
the selected Date (spec/05 comparison gate and spec/09 target rendering).
-/

namespace A12Kernel

inductive FullDateFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledSiteElabError)
  | targetNotFullDate (path : List String)
  | targetPolicy (cause : DateConstantTargetElabError)
  | unsupportedZone (zone : String)
  deriving Repr, DecidableEq

/-- One complete or component-omitting Date target and its exact-profile source at a checked site. -/
structure CheckedFullDateFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledSite model
  dateCarrier : shape.carrier.dateYearPresence?.isSome = true
  targetPolicy : CheckedDateConstantTarget model (shape.sourceProfile.dateYearPresence?.getD true)
  profile : ModelZone.ConcreteProfile
  profileMatches : ModelZone.ConcreteProfile.ofId? model.timeZoneId = some profile

/-- Check the site's supported Date profiles and the target's own storage policy, including its pre-1900
check. Year presence is compatible directly or through a declared Base Year; target spelling and
stored precision are independent of the exact source-list profile (spec/05, K11 target-profile capture). -/
def checkFullDateFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except FullDateFirstFilledComputationElabError (CheckedFullDateFirstFilledComputation model) := do
  let shape ← (checkTemporalFirstFilledSite model declaringGroup targetField authored
    (ownsBefore1900 := true)).mapError .shape
  if dateCarrier : shape.carrier.dateYearPresence?.isSome = true then
    let targetPolicy ← (elaborateDateConstantTargetIn model shape.site.target.repeatableScope
      targetField (shape.sourceProfile.dateYearPresence?.getD true)).mapError .targetPolicy
    match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
    | some profile => pure { shape, dateCarrier, targetPolicy, profile, profileMatches := hProfile }
    | none => throw (.unsupportedZone model.timeZoneId)
  else throw (.targetNotFullDate shape.site.target.path)

/-- Select the checked Date instant before the target renders it; a partial full-Date source is decoded
under its source spelling (spec/05 selection and spec/09 rendering). -/
def fullDateFirstFilledCellAt (format : FullDateTargetFormat)
    (profile : ModelZone.ConcreteProfile) (addressed : CheckedAddressedCell) : TemporalComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.date date)) => .value date.instant
  | .value (.partialDate text) =>
      match firstFilledPartialDateResolution format text with
      | some (.date date) =>
          match profile.resolveCompletedDateParts? date.civil.parts with
          | some value => .value value.instant
          | none => .poison .malformed
      | some .nonRelevant => .noValue
      | none => .poison .malformed
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Only an empty cell advances selection. A present unknown-year Date stops with no value,
as the partial-Date first-filled discriminator requires (spec/05, KF508). -/
def evalFullDateFirstFilledCells (format : FullDateTargetFormat)
    (profile : ModelZone.ConcreteProfile) :
    List CheckedAddressedCell → TemporalComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match fullDateFirstFilledCellAt format profile addressed with
      | .noValue =>
          if observeCell .computation addressed.cell = .empty then
            evalFullDateFirstFilledCells format profile remaining
          else .noValue
      | result => result

/-- A full-Date run's failure: the shared site's, or the target policy's rendering. -/
inductive FullDateFirstFilledComputationFault where
  | site (cause : FirstFilledSiteFault)
  | target (cause : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One instance's rendered Date outcome retained under its exact target address. -/
structure FullDateFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : FullDateTargetOutcome
  deriving Repr, DecidableEq

/-- One checked Date result backed by the common FullDate channels over exact cell addresses. -/
structure FullDateFirstFilledComputationRunView (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedFullDateFirstFilledComputation model
  fullDate : FullDateComputationRunView ResidualMessage CellAddr

namespace CheckedFullDateFirstFilledComputation

def targetField (operation : CheckedFullDateFirstFilledComputation model) : FieldId :=
  operation.shape.site.targetField

def target (operation : CheckedFullDateFirstFilledComputation model) : FlatFieldDecl :=
  operation.shape.site.target

def referencesWith (operation : CheckedFullDateFirstFilledComputation model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  operation.shape.referencesWith field filterReads

def referencesField (operation : CheckedFullDateFirstFilledComputation model) : FieldId → Bool :=
  fun field => operation.referencesWith field (·.referencesField field)

theorem excludesTarget (operation : CheckedFullDateFirstFilledComputation model) :
    operation.referencesWith operation.targetField (·.forbidsTarget operation.targetField) = false :=
  operation.shape.excludesTarget

/-- Scan the source at one target instance's environment, then render the selected Date. -/
def evaluateAt (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) (world : Option World := none) :
    Except FullDateFirstFilledComputationFault FullDateFirstFilledComputationOutcome := do
  let resolved ← (operation.shape.site.source.resolveAt input read environment world).mapError
    (.site ∘ .source)
  let outcome ← (operation.targetPolicy.evaluate operation.profile (evaluateFirstFilledSource resolved .poison (fun resolved =>
    evalFullDateFirstFilledCells (match operation.shape.sourceProfile with
      | .fullDate format => format
      | _ => .yearMonthDayDashes) operation.profile resolved.cells))).mapError
    .target
  pure { targetField := target, outcome }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    Except FullDateFirstFilledComputationFault (List FullDateFirstFilledComputationOutcome) :=
  operation.shape.site.instances input (.site ∘ .targetRows) (.site ∘ .targetEnvironment)
    (fun target _ => pure { targetField := target, outcome := .noValue })
    (operation.evaluateAt (world := world) input read)

def execute (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (world : Option World := none) :
    Except FullDateFirstFilledComputationFault (List FullDateFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read world

/-- Classify caller-view outcomes against immutable source target state through the shared FullDate
result owner. -/
def executeResultWithRead (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) (world : Option World := none) :
    Except FullDateFirstFilledComputationFault
      (FullDateFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read world
  pure { operation
         fullDate := FullDateComputationRunView.fromOutcomesAt input.sourceFullDateTargetStateAt
           residualMessages
           (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

def executeResult (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) (world : Option World := none) :
    Except FullDateFirstFilledComputationFault
      (FullDateFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages world

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
    (input : CheckedDocument model) (world : Option World := none) :
    Except FullDateFirstFilledCheckedResultFault
      (FullDateFirstFilledComputationRunView model ComputationFormalInputFinding) :=
  runWithFormalInputs operation.formalInputPlan input (operation.executeResultWithRead (world := world) input)

end CheckedFullDateFirstFilledComputation

end A12Kernel
