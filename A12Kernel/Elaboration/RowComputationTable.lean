import A12Kernel.Elaboration.RepeatableStringConstantComputation
import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.DocumentComputationStep
import A12Kernel.Elaboration.ComputationCondition

/-! # Checked alternatives at a repeatable non-Number target

Selection belongs to one target row. The existing constant and Enumeration operations keep their
certificates and evaluators; this table adds no token semantics or alternative-selection algorithm.
-/

namespace A12Kernel

inductive CheckedRowComputationOperation (model : FlatModel) where
  | stringConstant (operation : CheckedRepeatableStringConstantComputation model)
  | enumeration (operation : CheckedAddressedEnumerationComputation model)

namespace CheckedRowComputationOperation

def target : CheckedRowComputationOperation model → FieldId
  | .stringConstant operation => operation.checkedTarget.targetField
  | .enumeration operation => operation.target.field

def scope : CheckedRowComputationOperation model → List RepeatableLevel
  | .stringConstant operation => operation.checkedTarget.declaration.repeatableScope
  | .enumeration operation => operation.target.declaration.repeatableScope

def family : CheckedRowComputationOperation model → DocumentTargetFamily
  | .stringConstant _ => .string
  | .enumeration _ => .enumeration

def referencesField : CheckedRowComputationOperation model → FieldId → Bool
  | .stringConstant _, _ => false
  | .enumeration operation, field => operation.source.referencesField field

end CheckedRowComputationOperation

inductive RowComputationTableError where
  | empty
  | unguardedAlternative (index : Nat)
  | targetMismatch (index : Nat)
  | guardNotAdmitted (index : Nat)
  | guardTargetReference (index : Nat)
  deriving Repr, DecidableEq

/-- Each member retains the certificates needed by a consumer inspecting the authored table. -/
structure CheckedRowComputationAlternative (model : FlatModel) (target : FieldId)
    (scope : List RepeatableLevel) (family : DocumentTargetFamily) where
  operation : CheckedRowComputationOperation model
  precondition : Option ComputationCondition
  sameTarget : operation.target = target
  sameScope : operation.scope = scope
  sameFamily : operation.family = family
  guardBound : precondition.all (·.rowBoundBool model scope) = true
  guardExcludesTarget : precondition.any (·.forbidsTarget target) = false

def CheckedRowComputationAlternative.toResolved
    (alternative : CheckedRowComputationAlternative model target scope family) :
    ComputationAlternative (CheckedRowComputationOperation model) :=
  { operation := alternative.operation, precondition := alternative.precondition }

/-- A nonempty row table keeps its target identity and each member's checked guard and operation. -/
structure CheckedRowComputationTable (model : FlatModel) where
  target : FieldId
  scope : List RepeatableLevel
  family : DocumentTargetFamily
  first : CheckedRowComputationAlternative model target scope family
  remaining : List (CheckedRowComputationAlternative model target scope family)

private def certifyAlternative (target : FieldId) (scope : List RepeatableLevel)
    (family : DocumentTargetFamily) (guardRequired : Bool) (common : Option ComputationCondition)
    (alternative : ComputationAlternative (CheckedRowComputationOperation model)) (index : Nat) :
    Except RowComputationTableError (CheckedRowComputationAlternative model target scope family) := do
  if guardRequired && alternative.precondition.isNone then throw (.unguardedAlternative index)
  if hTarget : alternative.operation.target = target then
    if hScope : alternative.operation.scope = scope then
      if hFamily : alternative.operation.family = family then
        let guard := ComputationCondition.withCommon common alternative.precondition
        if hGuard : guard.all (·.rowBoundBool model scope) = true then
          if hSelf : guard.any (·.forbidsTarget target) = false then
            pure {
              operation := alternative.operation, precondition := guard
              sameTarget := hTarget, sameScope := hScope, sameFamily := hFamily,
              guardBound := hGuard, guardExcludesTarget := hSelf }
          else throw (.guardTargetReference index)
        else throw (.guardNotAdmitted index)
      else throw (.targetMismatch index)
    else throw (.targetMismatch index)
  else throw (.targetMismatch index)

/-- Check own guardedness before combining the common condition, as the existing String and Number
source tables do. Target-row binding and the target-read exemption use the shared guard owner. -/
def certifyRowComputationTable
    (alternatives : List (ComputationAlternative (CheckedRowComputationOperation model)))
    (common : Option ComputationCondition := none) :
    Except RowComputationTableError (CheckedRowComputationTable model) := do
  let some prototype := alternatives.head? | throw .empty
  let target := prototype.operation.target
  let scope := prototype.operation.scope
  let family := prototype.operation.family
  let checked ← alternatives.zipIdx |>.mapM fun (alternative, index) =>
    certifyAlternative target scope family (alternatives.length > 1) common alternative index
  let first :: remaining := checked | throw .empty
  pure { target, scope, family, first, remaining }

inductive RowComputationTableFault where
  | rows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | guardBinding (cause : ComputationConditionError)
  | targetPatternUnavailable (field : FieldId)
  | enumeration (cause : AddressedEnumerationComputationFault)
  | readBack (cause : DocumentComputationStepFault)
  deriving Repr, DecidableEq

namespace CheckedRowComputationOperation

/-- Evaluate only a selected operation; target checking cannot influence which alternative wins. -/
def evaluateAt (operation : CheckedRowComputationOperation model)
    (patterns : PreparedFlatStringPatterns model compilePattern) (document : CheckedDocument model)
    (environment : Env) : Except RowComputationTableFault (DocumentTargetOutcome × CheckedCell) := do
  match operation with
  | .stringConstant operation =>
      let some matcher := patterns.targetMatcher? operation.checkedTarget.targetField
        | throw (.targetPatternUnavailable operation.checkedTarget.targetField)
      let outcome := operation.outcomeWithPattern matcher
      pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)
  | .enumeration operation =>
      let result ← (operation.evaluateAtWithRead document.read environment).mapError .enumeration
      let outcome := result.result.asExactStringTargetOutcome
      pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)

end CheckedRowComputationOperation

namespace CheckedRowComputationTable

def alternatives (table : CheckedRowComputationTable model) :=
  (table.first :: table.remaining).map (·.toResolved)

def operationReferencesField (table : CheckedRowComputationTable model) (field : FieldId) : Bool :=
  table.alternatives.any (·.operation.referencesField field)

def protectionConditions (table : CheckedRowComputationTable model) : List (Option ComputationCondition) :=
  table.alternatives.map (·.precondition)

/-- Traverse the existing in-capacity row domain. An over-limit row clears without guard or operation
reads; an admitted row selects once using the same addressed overlay as the operation reads. -/
def execute (table : CheckedRowComputationTable model) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (document : CheckedDocument model) :
    Except RowComputationTableFault (List (CellAddr × DocumentTargetOutcome × CheckedCell)) :=
  let target := table.target
  let scope := table.scope
  let family := table.family
  let atRow (environment : Env) (outcome : DocumentTargetOutcome) (cell : CheckedCell) := do
    let path ← (environment.pathForScope scope).mapError RowComputationTableFault.environment
    pure ({ field := target, path }, outcome, cell)
  document.computationRowOutcomes scope .rows
    (fun environment => atRow environment family.noValue DocumentComputationReadBack.empty)
    (fun environment => do
      let context : ScalarComputationContext := {
        read := document.computationFillContext.read environment
        world := some world, row := environment, addressed := some document.computationFillContext }
      match ← (ComputationAlternative.selectFirstChecked table.alternatives context).mapError .guardBinding with
      | .noMatch => atRow environment family.noValue DocumentComputationReadBack.empty
      | .poison cause => atRow environment (family.poison cause) DocumentComputationReadBack.poison
      | .selected operation =>
          let (outcome, cell) ← operation.evaluateAt patterns document environment
          atRow environment outcome cell)

end CheckedRowComputationTable
end A12Kernel
