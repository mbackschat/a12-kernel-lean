import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.CheckedStarShape
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # Direct one-star ordinary String `FirstFilledValue` computation -/

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
  deriving Repr, DecidableEq

/-- One fixed ordinary String target and one direct single-level ordinary String star. -/
structure CheckedStringFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  /-- The group the computation is declared in, which the target need not lie in. -/
  declaringGroup : GroupPath
  /-- The declaring group is a representable path, certified by the star elaboration above rather
  than re-tested here. Placement itself is unconstrained; only representability survives. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetFixed : target.repeatableScope = []
  targetOrdinary : target.isOrdinaryStringComputationCarrier = true
  sourceOrdinary : source.declaration.isOrdinaryStringComputationCarrier = true
  sourceDirectSingleStar : source.isDirectSingleStar = true

/-- Check the fixed target and direct-star source without collapsing ordinary String target policy into exact-token acceptance. -/
def checkStringFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except StringFirstFilledComputationElabError
      (CheckedStringFirstFilledComputation model) := do
  match hStar : elaborateStarFieldPath model declaringGroup authored with
  | .error cause => .error (.source cause)
  | .ok source => do
    let target ← model.lookupUniqueId targetField |>.mapError .target
    -- No placement test. `elaborateStarFieldPath` already rejects an unrepresentable declaring
    -- group, and placement itself is unconstrained here: a fixed target under a star aggregate
    -- derives no iteration, so the Kernel admits it from an unrelated group.
    if hFixed : target.repeatableScope = [] then
      if hTarget : target.isOrdinaryStringComputationCarrier = true then
        if hSource : source.declaration.isOrdinaryStringComputationCarrier = true then
          if hShape : source.isDirectSingleStar = true then
            pure {
              target
              source
              declaringGroup
              declaringGroupValid :=
                elaborateStarFieldPath_declaringGroupValid hStar
              targetFixed := hFixed
              targetOrdinary := hTarget
              sourceOrdinary := hSource
              sourceDirectSingleStar := hShape
            }
          else
            throw (.sourceShape source.declaration.path)
        else
          throw (.sourceNotOrdinaryString source.declaration.path)
      else
        throw (.targetNotOrdinaryString target.path)
    else
      throw (.targetRepeatable target.path)

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
    (resolved : ResolvedCheckedStarField) : TokenComputationResult :=
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map fun cell => stringFirstFilledCellAt cell.cell
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  (evalFirstFilledToken side).asComputationResult

/-- Select the first filled source, then run the exact declaration-owned String target policy and prepared matcher. -/
def execute (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except StringFirstFilledComputationFault StringTargetOutcome := do
  let matcher ← match patterns.targetMatcher? operation.target.id with
    | some matcher => pure matcher
    | none => throw (.targetPatternUnavailable operation.target.id)
  let resolved ← operation.source.resolveCheckedField input []
    |>.mapError .source
  pure (operation.target.stringPolicy.checkTargetWithPattern matcher
    (evalResolvedStringFirstFilled resolved).asStringStore)

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
