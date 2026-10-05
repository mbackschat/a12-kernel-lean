import A12Kernel.Elaboration.RepeatableStringConstantComputation
import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.DocumentComputationStep
import A12Kernel.Elaboration.ComputationNumericGuard
import A12Kernel.Elaboration.BooleanConstantComputation

/-! # Checked alternatives at non-Number target instances

Selection belongs to one target instance; fixed Boolean/Confirm and temporal targets have the empty address. Temporal expressions, bound String expressions, String/Boolean/Confirm constants and Enumeration operations
keep their certificates and evaluators; this table adds no token semantics or selection algorithm.
-/

namespace A12Kernel

inductive CheckedRowComputationOperation (model : FlatModel) where
  | stringExpression (operation : CheckedRowStringExpression model)
  | stringConstant (operation : CheckedRepeatableStringConstantComputation model)
  | enumeration (operation : CheckedAddressedEnumerationComputation model)
  | booleanConstant (operation : CheckedRepeatableBooleanConstantComputation model)
  | fixedBooleanConstant (operation : CheckedBooleanConstantComputation model)
  | temporalExpression (operation : CheckedTemporalExpressionComputation model)
  | dateRangeConstruction (operation : CheckedBoundDateRangeConstructionComputation model)

namespace CheckedRowComputationOperation

def target : CheckedRowComputationOperation model → FieldId
  | .stringExpression operation => operation.target.targetField
  | .stringConstant operation => operation.checkedTarget.targetField
  | .enumeration operation => operation.target.field
  | .booleanConstant operation => operation.checkedTarget.targetField
  | .fixedBooleanConstant operation => operation.target.id
  | .dateRangeConstruction operation => operation.target.source.id
  | .temporalExpression operation => operation.target

def scope : CheckedRowComputationOperation model → List RepeatableLevel
  | .stringExpression operation => operation.target.declaration.repeatableScope
  | .stringConstant operation => operation.checkedTarget.declaration.repeatableScope
  | .enumeration operation => operation.target.declaration.repeatableScope
  | .booleanConstant operation => operation.checkedTarget.declaration.repeatableScope
  | .fixedBooleanConstant _ => []
  | .dateRangeConstruction operation => operation.target.declaration.repeatableScope
  | .temporalExpression operation => operation.scope

def family : CheckedRowComputationOperation model → DocumentTargetFamily
  | .stringExpression _ | .stringConstant _ => .string
  | .enumeration _ => .enumeration
  | .booleanConstant _ | .fixedBooleanConstant _ => .boolean
  | .dateRangeConstruction _ => .dateRange
  | .temporalExpression operation => operation.family

def referencesField : CheckedRowComputationOperation model → FieldId → Bool
  | .stringExpression operation, field => operation.expression.referencesField field
  | .stringConstant _, _ | .booleanConstant _, _ | .fixedBooleanConstant _, _ => false
  | .enumeration operation, field => operation.source.referencesField field
  | .dateRangeConstruction operation, field => operation.referencesField field
  | .temporalExpression operation, field => operation.expression.referencesField field

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
  precondition : Option (CheckedComputationCondition model)
  sameTarget : operation.target = target
  sameScope : operation.scope = scope
  sameFamily : operation.family = family
  guardBound : precondition.all (·.rowBoundBool scope) = true
  guardExcludesTarget : precondition.any (·.forbidsTarget target) = false

def CheckedRowComputationAlternative.toResolved
    (alternative : CheckedRowComputationAlternative model target scope family) :
    CheckedComputationAlternative model (CheckedRowComputationOperation model) :=
  { operation := alternative.operation, precondition := alternative.precondition }

/-- A nonempty row table keeps its target identity and each member's checked guard and operation. -/
structure CheckedRowComputationTable (model : FlatModel) where
  target : FieldId
  scope : List RepeatableLevel
  family : DocumentTargetFamily
  first : CheckedRowComputationAlternative model target scope family
  remaining : List (CheckedRowComputationAlternative model target scope family)

private def certifyAlternative (target : FieldId) (scope : List RepeatableLevel)
    (family : DocumentTargetFamily) (guardRequired : Bool) (common : Option (CheckedComputationCondition model))
    (alternative : CheckedComputationAlternative model (CheckedRowComputationOperation model)) (index : Nat) :
    Except RowComputationTableError (CheckedRowComputationAlternative model target scope family) := do
  if guardRequired && alternative.precondition.isNone then throw (.unguardedAlternative index)
  if hTarget : alternative.operation.target = target then
    if hScope : alternative.operation.scope = scope then
      if hFamily : alternative.operation.family = family then
        let guard := CheckedComputationCondition.withCommon common alternative.precondition
        if hGuard : guard.all (·.rowBoundBool scope) = true then
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
    (alternatives : List (CheckedComputationAlternative model (CheckedRowComputationOperation model)))
    (common : Option (CheckedComputationCondition model) := none) :
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
  | stringExpression (error : StringComputationFault)
  | rows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | guardBinding (cause : CheckedComputationConditionError)
  | targetPatternUnavailable (field : FieldId)
  | dateRangeConstruction (cause : DateRangeConstructionComputationFault)
  | enumeration (cause : AddressedEnumerationComputationFault)
  | readBack (cause : DocumentComputationStepFault)
  deriving Repr, DecidableEq

namespace CheckedRowComputationOperation

private def booleanOutcome (operation : BooleanConstantOperation) : DocumentTargetOutcome × CheckedCell :=
  let outcome := BooleanComputationOutcome.value operation.value
  (.boolean outcome, DocumentComputationReadBack.booleanConstant operation outcome)

/-- Evaluate only a selected operation; target checking cannot influence which alternative wins. -/
def evaluateAt (operation : CheckedRowComputationOperation model) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (document : CheckedDocument model)
    (environment : Env) : Except RowComputationTableFault (DocumentTargetOutcome × CheckedCell) := do
  match operation with
  | .stringExpression operation =>
      let field := operation.target.targetField
      let some matcher := patterns.targetMatcher? field | throw (.targetPatternUnavailable field)
      let context := document.computationContextAt environment
      let result ← (operation.expression.eval .computation { read := context.read } context.numberText).mapError .stringExpression
      let term := StringTerm.ofOperand result
      let outcome := operation.target.declaration.checkStringExpressionTarget matcher term.store
      pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)
  | .stringConstant operation =>
      let some matcher := patterns.targetMatcher? operation.checkedTarget.targetField
        | throw (.targetPatternUnavailable operation.checkedTarget.targetField)
      let outcome := operation.outcomeWithPattern matcher
      pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)
  | .booleanConstant operation => pure (booleanOutcome operation.operation.operation)
  | .fixedBooleanConstant operation => pure (booleanOutcome operation.operation.operation)
  | .temporalExpression operation =>
      let context := document.computationContextAt environment
      (operation.run (context.withWorld world)).mapError .readBack
  | .dateRangeConstruction operation =>
      let outcome ← (operation.evaluateWith (document.computationContextAt environment).read).mapError .dateRangeConstruction
      pure (.dateRange outcome, ← (DocumentComputationReadBack.dateRange model operation.target.policy outcome).mapError .readBack)
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

def protectionConditions (table : CheckedRowComputationTable model) : List (Option (CheckedComputationCondition model)) :=
  table.alternatives.map (·.precondition)

/-- Traverse the existing target domain, including the fixed empty address. An over-limit row clears without guard or operation
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
  document.computationTargetOutcomes scope .rows
    (fun environment => atRow environment family.noValue DocumentComputationReadBack.empty)
    (fun environment => do
      let context := (document.computationContextAt environment).withWorld world
      match CheckedComputationAlternative.selectFirstChecked table.alternatives context with
      | .error (.predicate .valueFailure) => atRow environment (.valueError family) DocumentComputationReadBack.poison
      | .error error => throw (.guardBinding error)
      | .ok .noMatch => atRow environment family.noValue DocumentComputationReadBack.empty
      | .ok (.poison cause) => atRow environment (family.poison cause) DocumentComputationReadBack.poison
      | .ok (.selected operation) =>
          let (outcome, cell) ← operation.evaluateAt world patterns document environment
          atRow environment outcome cell)

end CheckedRowComputationTable
end A12Kernel
