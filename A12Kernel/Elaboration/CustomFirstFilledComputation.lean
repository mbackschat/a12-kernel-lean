import A12Kernel.Elaboration.FirstFilledPlacement
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # Custom `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes through the shared first-filled site. Selected entity
lists retain the registered Custom payload contract; their Custom calibration is internal
only. The shared source/placement owner keeps lookup dependencies separate from payload kinds. -/

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

/-- Check exact Custom declaration agreement after shared source admission. The validated model
already guarantees that each Custom declaration is an evaluated String field. -/
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
    (target : CellAddr) (environment : Env) (world : Option World := none) :
    Except FirstFilledSiteFault AddressedTokenComputationOutcome := do
  let resolved ← (operation.site.source.resolveAt input read environment world).mapError .source
  let result := evaluateFirstFilledSource resolved TokenComputationResult.poison fun resolved =>
    let side : ResolvedValueListSide .token := {
      cells := resolved.cells.map fun cell => customFirstFilledCellAt cell.cell
      hasUninstantiatedTail := resolved.hasOpenTail
      hasHaving := false }
    (evalFirstFilledToken side).asComputationResult
  pure { targetField := target, result }


/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    Except FirstFilledSiteFault (List AddressedTokenComputationOutcome) :=
  operation.site.instances input .targetRows .targetEnvironment
    (fun target _ => pure { targetField := target, result := .noValue })
    (operation.evaluateAt (world := world) input read)

def execute (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (world : Option World := none) :
    Except FirstFilledSiteFault (List AddressedTokenComputationOutcome) :=
  operation.executeWithRead input input.read world

/-- Classify caller-view token outcomes against the immutable source target at the same addresses.
The matching Custom declaration makes a separately rejected target outcome unreachable. -/
def executeResultWithRead (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) (world : Option World := none) :
    Except FirstFilledSiteFault (CustomFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read world
  pure { operation, string := projectAddressedTokenResults input residualMessages outcomes }

def executeResult (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) (world : Option World := none) :
    Except FirstFilledSiteFault (CustomFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages world

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
abbrev CustomFirstFilledCheckedResultFault := ComputationFormalInputRunFault FirstFilledSiteFault

namespace CheckedCustomFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedCustomFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  operation.site.formalInputPlan

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (world : Option World := none) :
    Except CustomFirstFilledCheckedResultFault
      (CustomFirstFilledComputationRunView model ComputationFormalInputFinding) :=
  runWithFormalInputs operation.formalInputPlan input (operation.executeResultWithRead (world := world) input)

end CheckedCustomFirstFilledComputation

end A12Kernel
