import A12Kernel.Elaboration.FirstFilledFieldSource
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # Fixed-target ordinary String `FirstFilledValue` computation

The source is a direct single-level star or a direct list of plain nonrepeatable fields, read through
the shared [`FirstFilledFieldSource`](FirstFilledFieldSource.lean); the list is measured at a join, a
cleared upstream falling through and a poisoned one ending the scan
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-extractor-join)). -/

namespace A12Kernel

/-- The declaration-local ordinary evaluated-String carrier shared by fixed and addressed String first-filled targets. -/
def FlatFieldDecl.isOrdinaryStringComputationCarrier
    (declaration : FlatFieldDecl) : Bool :=
  declaration.policy.kind == .string &&
    declaration.stringValueMode == .evaluated &&
    declaration.customType.isNone && declaration.enumeration.isNone

inductive StringFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | targetNotOrdinaryString (path : List String)
  | source (cause : StarPathElabError)
  | sourceNotOrdinaryString (path : List String)
  | sourceShape (path : List String)
  /-- A list source the shared entity list or its plain-field reading refuses. -/
  | list (cause : FirstFilledListElabError)
  /-- A list source naming the target itself. -/
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

/-- Project the source star's own refusals, whose classes belong to the path rather than the
    carrier: an unstarred level below the first star is the missing-star class on every carrier
    measured, the String `FirstFilledValue` computation among them
    ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)).
    The other refusals stay unmapped. -/
def StringFirstFilledComputationElabError.diagnostic? :
    StringFirstFilledComputationElabError → Option KernelStaticDiagnostic
  | .source cause => cause.diagnostic?
  -- Named rather than wildcarded, so a new refusal must be classified rather than absorbed. None of
  -- these is measured on this carrier.
  | .target _ | .targetRepeatable _ | .targetNotOrdinaryString _ | .sourceNotOrdinaryString _
  | .sourceShape _ | .list _ | .targetSelfReference _ => none

/-- One fixed ordinary String target and one ordinary String source, a direct single-level star or a
direct list of plain nonrepeatable fields, certified against the same model. -/
structure CheckedStringFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : FirstFilledFieldSource model
  /-- The group the computation is declared in, which the target need not lie in. -/
  declaringGroup : GroupPath
  /-- The declaring group is a representable path, certified by the source's elaboration rather
  than re-tested here. Placement itself is unconstrained; only representability survives. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetFixed : target.repeatableScope = []
  targetOrdinary : target.isOrdinaryStringComputationCarrier = true
  sourceOrdinary : source.declarations.all (·.isOrdinaryStringComputationCarrier) = true
  sourceShape : source.admittedShape = true
  excludesTarget : source.referencesField target.id = false

private def checkStringFirstFilledSourceAgainst (model : FlatModel) (target : FlatFieldDecl)
    (declaringGroup : GroupPath) (declaringGroupValid : GroupPath.isValid declaringGroup = true)
    (source : FirstFilledFieldSource model) :
    Except StringFirstFilledComputationElabError (CheckedStringFirstFilledComputation model) := do
  if hFixed : target.repeatableScope = [] then
    if hTarget : target.isOrdinaryStringComputationCarrier = true then
      if hSource : source.declarations.all (·.isOrdinaryStringComputationCarrier) = true then
        if hShape : source.admittedShape = true then
          if hExcludes : source.referencesField target.id = false then
            pure {
              target, source, declaringGroup, declaringGroupValid
              targetFixed := hFixed
              targetOrdinary := hTarget
              sourceOrdinary := hSource
              sourceShape := hShape
              excludesTarget := hExcludes }
          else throw (.targetSelfReference target.path)
        else throw (.sourceShape (source.declarations.head?.map (·.path) |>.getD target.path))
      else
        let other :=
          (source.declarations.find? (!·.isOrdinaryStringComputationCarrier)).getD target
        throw (.sourceNotOrdinaryString other.path)
    else
      throw (.targetNotOrdinaryString target.path)
  else
    throw (.targetRepeatable target.path)

/-- Check the fixed target and its star or list source without collapsing ordinary String target
policy into exact-token acceptance. -/
def checkStringFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except StringFirstFilledComputationElabError
      (CheckedStringFirstFilledComputation model) := do
  match authored with
  | .star path =>
    match hStar : elaborateStarFieldPath model declaringGroup path with
    | .error cause => .error (.source cause)
    | .ok source => do
      let target ← model.lookupUniqueId targetField |>.mapError .target
      -- No placement test. `elaborateStarFieldPath` already rejects an unrepresentable declaring
      -- group, and placement itself is unconstrained here: a fixed target under a star aggregate
      -- derives no iteration, so the Kernel admits it from an unrelated group.
      checkStringFirstFilledSourceAgainst model target declaringGroup
        (elaborateStarFieldPath_declaringGroupValid hStar) (.star source)
  | .list list => do
    -- As on the Boolean carrier: the list resolves at the target's group first, the target after it.
    let targetGroup :=
      ((model.lookupUniqueId targetField).toOption.map (·.groupPath)).getD declaringGroup
    let checked ← elaborateFirstFilledFieldList model declaringGroup targetGroup list
      |>.mapError .list
    let target ← model.lookupUniqueId targetField |>.mapError .target
    checkStringFirstFilledSourceAgainst model target declaringGroup checked.declaringGroupValid
      (.list checked.fields)

/-- Classify one prepared ordinary String source cell for computation-phase first-filled selection. -/
def stringFirstFilledCellAt (cell : CheckedCell) : ValueListCell .token :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.str value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

namespace TokenComputationResult

/-- Convert selection into the ordinary String root-store domain before target policy runs. -/
def asStringStore : TokenComputationResult → StringStore
  | .value token =>
      if nonempty : token ≠ "" then .produced { text := token, nonempty }
      else .noValue
  | .noValue => .noValue
  | .poison cause => .poison cause

end TokenComputationResult

inductive StringFirstFilledComputationFault where
  | source (cause : CheckedStarDocumentError)
  | targetPatternUnavailable (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked ordinary String first-filled result retaining its admitted operation. -/
structure StringFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedStringFirstFilledComputation model
  string : StringComputationRunView ResidualMessage

namespace CheckedStringFirstFilledComputation

/-- Evaluate a resolved source through the shared ordered token scan. -/
def evalResolvedStringFirstFilled
    (resolved : ResolvedFirstFilledSource) : TokenComputationResult :=
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map fun cell => stringFirstFilledCellAt cell.cell
    hasUninstantiatedTail := resolved.hasOpenTail
    hasHaving := false
  }
  (evalFirstFilledToken side).asComputationResult

/-- Select the first filled source, then run the exact declaration-owned String target policy and the
target's already recovered matcher. -/
def executeWith (operation : CheckedStringFirstFilledComputation model)
    (matcher : Option (String → Bool)) (input : CheckedDocument model) :
    Except StringFirstFilledComputationFault StringTargetOutcome := do
  let resolved ← operation.source.resolve input |>.mapError .source
  pure (operation.target.stringPolicy.checkTargetWithPattern matcher
    (evalResolvedStringFirstFilled resolved).asStringStore)

/-- Select the first filled source, then run the exact declaration-owned String target policy and prepared matcher. -/
def execute (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except StringFirstFilledComputationFault StringTargetOutcome := do
  let matcher ← match patterns.targetMatcher? operation.target.id with
    | some matcher => pure matcher
    | none => throw (.targetPatternUnavailable operation.target.id)
  operation.executeWith matcher input

/-- Classify the rich target outcome relative to the immutable source target. -/
def executeResult (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except StringFirstFilledComputationFault
      (StringFirstFilledComputationRunView model ResidualMessage) := do
  let outcome ← operation.execute patterns input
  pure {
    operation
    string := StringComputationRunView.fromSourcedOutcomes residualMessages [{
      targetField := operation.target.id
      outcome
      source := input.sourceStringTargetState operation.target.id
    }]
  }

end CheckedStringFirstFilledComputation

namespace StringFirstFilledComputationRunView

/-- Apply retained source-relative actions to a separate checked destination without reclassifying against it. -/
def applyToChecked
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError FieldId)
      (StringComputationDestination FieldId) :=
  view.string.applyTo destination.sourceStringTargetState

end StringFirstFilledComputationRunView

end A12Kernel
