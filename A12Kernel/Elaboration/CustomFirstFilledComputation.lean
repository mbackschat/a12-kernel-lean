import A12Kernel.Elaboration.FirstFilledFieldSource
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # Fixed-target Custom `FirstFilledValue` computation

The source is a direct single-level star or a direct list of plain nonrepeatable fields, read through
the shared [`FirstFilledFieldSource`](FirstFilledFieldSource.lean); the list is measured at a join
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-extractor-join)). -/

namespace A12Kernel

inductive CustomFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | targetNotCustom (path : List String)
  | source (cause : StarPathElabError)
  | sourceCustomTypeMismatch (path : List String)
      (expected : CustomFieldTypeDeclaration)
      (actual : Option CustomFieldTypeDeclaration)
  | sourceShape (path : List String)
  /-- A list source the shared entity list or its plain-field reading refuses. -/
  | list (cause : FirstFilledListElabError)
  /-- A list source naming the target itself. -/
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

/-- One fixed Custom target and one source carrying the same Custom declaration, a direct single-level
star or a direct list of plain nonrepeatable fields. -/
structure CheckedCustomFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : FirstFilledFieldSource model
  customType : CustomFieldTypeDeclaration
  /-- The group the computation is declared in, which the target need not lie in. -/
  declaringGroup : GroupPath
  /-- The declaring group is a representable path, certified by the source's elaboration rather
  than re-tested here. Placement itself is unconstrained; only representability survives. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetCustom : target.customType = some customType
  targetFixed : target.repeatableScope = []
  sourceCustom : source.declarations.all (·.customType == some customType) = true
  sourceShape : source.admittedShape = true
  excludesTarget : source.referencesField target.id = false

private def checkCustomFirstFilledSourceAgainst (model : FlatModel) (target : FlatFieldDecl)
    (declaringGroup : GroupPath) (declaringGroupValid : GroupPath.isValid declaringGroup = true)
    (source : FirstFilledFieldSource model) :
    Except CustomFirstFilledComputationElabError (CheckedCustomFirstFilledComputation model) := do
  if hFixed : target.repeatableScope = [] then
    match hTarget : target.customType with
    | none => throw (.targetNotCustom target.path)
    | some customType =>
      if hSource : source.declarations.all (·.customType == some customType) = true then
        if hShape : source.admittedShape = true then
          if hExcludes : source.referencesField target.id = false then
            pure {
              target, source, customType, declaringGroup, declaringGroupValid
              targetCustom := hTarget
              targetFixed := hFixed
              sourceCustom := hSource
              sourceShape := hShape
              excludesTarget := hExcludes }
          else throw (.targetSelfReference target.path)
        else throw (.sourceShape (source.declarations.head?.map (·.path) |>.getD target.path))
      else
        let other := (source.declarations.find? (·.customType != some customType)).getD target
        throw (.sourceCustomTypeMismatch other.path customType other.customType)
  else
    throw (.targetRepeatable target.path)

/-- Check the measured Custom computation shapes, a direct single-level star or a direct list. The
validated model already guarantees that every Custom declaration is an evaluated String field. -/
def checkCustomFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except CustomFirstFilledComputationElabError
      (CheckedCustomFirstFilledComputation model) := do
  match authored with
  | .star path =>
    match hStar : elaborateStarFieldPath model declaringGroup path with
    | .error cause => .error (.source cause)
    | .ok source => do
      let target ← model.lookupUniqueId targetField |>.mapError .target
      -- No placement test. `elaborateStarFieldPath` already rejects an unrepresentable declaring
      -- group, and placement itself is unconstrained here: a fixed target under a star aggregate
      -- derives no iteration, so the Kernel admits it from an unrelated group.
      checkCustomFirstFilledSourceAgainst model target declaringGroup
        (elaborateStarFieldPath_declaringGroupValid hStar) (.star source)
  | .list list => do
    -- As on the Boolean carrier: the list resolves at the target's group first, the target after it.
    let targetGroup :=
      ((model.lookupUniqueId targetField).toOption.map (·.groupPath)).getD declaringGroup
    let checked ← elaborateFirstFilledFieldList model declaringGroup targetGroup list
      |>.mapError .list
    let target ← model.lookupUniqueId targetField |>.mapError .target
    checkCustomFirstFilledSourceAgainst model target declaringGroup checked.declaringGroupValid
      (.list checked.fields)

/-- Classify one already prepared Custom source cell for computation-phase first-filled selection. -/
def customFirstFilledCellAt (cell : CheckedCell) : ValueListCell .token :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.str value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- One checked Custom `FirstFilledValue` result backed by the common String-shaped public channels. Retaining the private checked operation keeps every action tied to its exact admitted target and Custom declaration. -/
structure CustomFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedCustomFirstFilledComputation model
  string : StringComputationRunView ResidualMessage

namespace CheckedCustomFirstFilledComputation

/-- Execute the checked source over immutable rows without resampling its registered validator. -/
def execute (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TokenComputationResult := do
  let resolved ← operation.source.resolve input
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map fun cell => customFirstFilledCellAt cell.cell
    hasUninstantiatedTail := resolved.hasOpenTail
    hasHaving := false
  }
  pure (evalFirstFilledToken side).asComputationResult

/-- Execute one checked Custom selection and classify its exact token relative to the immutable source target. The matching Custom declaration makes a separately rejected target outcome unreachable. -/
def executeResult (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except CheckedStarDocumentError
      (CustomFirstFilledComputationRunView model ResidualMessage) := do
  let result ← operation.execute input
  let string := StringComputationRunView.fromSourcedOutcomes residualMessages [{
    targetField := operation.target.id
    outcome := result.asExactStringTargetOutcome
    source := input.sourceStringTargetState operation.target.id
  }]
  pure {
    operation
    string
  }

end CheckedCustomFirstFilledComputation

namespace CustomFirstFilledComputationRunView

/-- Apply retained source-relative Custom actions to a separately supplied checked document of the same model. The result is the exact root text-state projection and does not resample the registered validator or run implicit validation. -/
def applyToChecked
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError FieldId)
      (StringComputationDestination FieldId) :=
  view.string.applyTo destination.sourceStringTargetState

end CustomFirstFilledComputationRunView

end A12Kernel
