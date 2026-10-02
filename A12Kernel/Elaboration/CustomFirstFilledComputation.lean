import A12Kernel.Elaboration.FirstFilledPlacement
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # Custom `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes over the shared first-filled site: a fixed target over a
direct single-level star or a list of plain nonrepeatable fields, a repeatable one over a sibling star
at every row of its scope. The list is measured at a join
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-extractor-join)). -/

namespace A12Kernel

inductive CustomFirstFilledComputationElabError where
  | site (cause : FirstFilledPlacementElabError)
  | targetNotCustom (path : List String)
  | sourceCustomTypeMismatch (path : List String)
      (expected : CustomFieldTypeDeclaration)
      (actual : Option CustomFieldTypeDeclaration)
  /-- A list source naming the target itself. -/
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

/-- One Custom target, fixed or repeatable, and one source carrying the same Custom declaration,
placed on the shared site. -/
structure CheckedCustomFirstFilledComputation (model : FlatModel) where
  private mk ::
  site : CheckedFirstFilledSite model
  customType : CustomFieldTypeDeclaration
  targetCustom : site.target.customType = some customType
  sourceCustom : site.source.declarations.all (·.customType == some customType) = true
  excludesTarget : site.referencesField site.targetField = false

/-- Check the measured Custom computation shapes: a direct single-level star or a direct list at a
fixed target, a sibling star at a repeatable one. The validated model already guarantees that every
Custom declaration is an evaluated String field. -/
def checkCustomFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except CustomFirstFilledComputationElabError
      (CheckedCustomFirstFilledComputation model) := do
  -- The target's Custom declaration is checked before its placement, so a non-Custom target is
  -- refused as such wherever it sits.
  if let .ok target := model.lookupUniqueId targetField then
    if target.customType.isNone then throw (.targetNotCustom target.path)
  let site ← (checkFirstFilledSite model declaringGroup targetField authored).mapError .site
  match hTarget : site.target.customType with
  | none => throw (.targetNotCustom site.target.path)
  | some customType =>
    if hSource : site.source.declarations.all (·.customType == some customType) = true then
      if hExcludes : site.referencesField site.targetField = false then
        pure { site, customType, targetCustom := hTarget, sourceCustom := hSource
               excludesTarget := hExcludes }
      else throw (.targetSelfReference site.target.path)
    else
      let other := (site.source.declarations.find? (·.customType != some customType)).getD site.target
      throw (.sourceCustomTypeMismatch other.path customType other.customType)

/-- Classify one already prepared Custom source cell for computation-phase first-filled selection. -/
def customFirstFilledCellAt (cell : CheckedCell) : ValueListCell .token :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.str value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- One checked Custom `FirstFilledValue` result backed by the common String-shaped public channels
over exact cell addresses. Retaining the private checked operation keeps every action tied to its exact
admitted target and Custom declaration. -/
structure CustomFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedCustomFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedCustomFirstFilledComputation

def targetField (operation : CheckedCustomFirstFilledComputation model) : FieldId :=
  operation.site.targetField

def target (operation : CheckedCustomFirstFilledComputation model) : FlatFieldDecl :=
  operation.site.target

def referencesField (operation : CheckedCustomFirstFilledComputation model) : FieldId → Bool :=
  operation.site.referencesField

/-- Scan the source at one target instance's environment without resampling its registered
validator. -/
def evaluateAt (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) :
    Except FirstFilledSiteFault AddressedTokenComputationOutcome := do
  let resolved ← (operation.site.source.resolveAt input read environment).mapError .source
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map fun cell => customFirstFilledCellAt cell.cell
    hasUninstantiatedTail := resolved.hasOpenTail
    hasHaving := false
  }
  pure { targetField := target, result := (evalFirstFilledToken side).asComputationResult }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except FirstFilledSiteFault (List AddressedTokenComputationOutcome) :=
  operation.site.instances input .targetRows .targetEnvironment
    (fun target _ => pure { targetField := target, result := .noValue })
    (operation.evaluateAt input read)

def execute (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FirstFilledSiteFault (List AddressedTokenComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view token outcomes against the immutable source target at the same addresses.
The matching Custom declaration makes a separately rejected target outcome unreachable. -/
def executeResultWithRead (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault (CustomFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure { operation, string := projectAddressedTokenResults input residualMessages outcomes }

def executeResult (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except FirstFilledSiteFault (CustomFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedCustomFirstFilledComputation

namespace CustomFirstFilledComputationRunView

/-- Apply retained source-relative Custom actions to a separately supplied checked document of the
same model. The result is an exact text-state projection and does not resample the registered
validator or run implicit validation. -/
def applyToChecked
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end CustomFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with Custom `FirstFilledValue`. -/
inductive CustomFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : FirstFilledSiteFault)
  deriving Repr, DecidableEq

namespace CheckedCustomFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedCustomFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    (operation.site.source.declarations.map (·.id)) [operation.targetField]

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CustomFirstFilledCheckedResultFault
      (CustomFirstFilledComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .error cause => .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedCustomFirstFilledComputation

end A12Kernel
