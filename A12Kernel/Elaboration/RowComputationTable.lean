import A12Kernel.Elaboration.RepeatableStringConstantComputation
import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.FirstFilledAlternative
import A12Kernel.Elaboration.ScalarCopyComputation
import A12Kernel.Elaboration.ComputationNumericGuard
import A12Kernel.Elaboration.BooleanConstantComputation
import A12Kernel.Elaboration.DateLiteralComputation
import A12Kernel.Elaboration.StringComputationTable

/-! # Checked alternatives at non-Number target instances

Selection belongs to one target instance; fixed Enumeration, Boolean/Confirm and temporal targets have the empty address. Temporal expressions, bound String expressions, String/Boolean/Confirm constants and Enumeration operations
keep their certificates and evaluators; this table adds no token semantics or selection algorithm.
-/

namespace A12Kernel

inductive CheckedRowComputationOperation (model : FlatModel) where
  | document (operation : CheckedDocumentComputationStep model)
  | fixedString (table : CheckedStringComputationTable model)
      (alternative : CheckedStringComputationAlternative model table.targetField)
  | scalarCopy (operation : CheckedScalarCopyComputation model)
  | firstFilled (operation : CheckedFirstFilledAlternative model)
  | stringExpression (operation : CheckedRowStringExpression model)
  | stringConstant (operation : CheckedRepeatableStringConstantComputation model)
  | enumeration (operation : CheckedAddressedEnumerationComputation model)
  | fixedEnumeration (operation : CheckedEnumerationComputationOperation model)
  | booleanConstant (operation : CheckedRepeatableBooleanConstantComputation model)
  | fixedBooleanConstant (operation : CheckedBooleanConstantComputation model)
  | temporalExpression (operation : CheckedTemporalExpressionComputation model)
  | dateLiteral (operation : CheckedDateLiteralComputation model)
  | dateRangeConstruction (operation : CheckedBoundDateRangeConstructionComputation model)

namespace CheckedRowComputationOperation

def target : CheckedRowComputationOperation model → FieldId
  | .document operation => operation.target
  | .fixedString table _ => table.targetField
  | .scalarCopy operation => operation.target.id
  | .firstFilled operation => operation.target.id
  | .stringExpression operation => operation.targetField
  | .stringConstant operation => operation.checkedTarget.targetField
  | .enumeration operation => operation.target.field
  | .fixedEnumeration operation => operation.target.field
  | .booleanConstant operation => operation.checkedTarget.targetField
  | .fixedBooleanConstant operation => operation.target.id
  | .dateRangeConstruction operation => operation.target.source.id
  | .temporalExpression operation => operation.target
  | .dateLiteral operation => operation.target.id

def scope : CheckedRowComputationOperation model → List RepeatableLevel
  | .document _ | .fixedString _ _ => []
  | .scalarCopy operation => operation.target.repeatableScope
  | .firstFilled operation => operation.target.repeatableScope
  | .stringExpression operation => operation.target.repeatableScope
  | .stringConstant operation => operation.checkedTarget.declaration.repeatableScope
  | .enumeration operation => operation.target.declaration.repeatableScope
  | .fixedEnumeration _ => []
  | .booleanConstant operation => operation.checkedTarget.declaration.repeatableScope
  | .fixedBooleanConstant _ => []
  | .dateRangeConstruction operation => operation.target.declaration.repeatableScope
  | .temporalExpression operation => operation.scope
  | .dateLiteral operation => operation.target.repeatableScope

def family : CheckedRowComputationOperation model → DocumentTargetFamily
  | .document operation => operation.family
  | .fixedString _ _ => .string
  | .scalarCopy operation => operation.family
  | .firstFilled operation => operation.family
  | .stringExpression _ | .stringConstant _ => .string
  | .enumeration _ | .fixedEnumeration _ => .enumeration
  | .booleanConstant _ | .fixedBooleanConstant _ => .boolean
  | .dateRangeConstruction _ => .dateRange
  | .temporalExpression operation => operation.family
  | .dateLiteral _ => .fullDate

def referencesField : CheckedRowComputationOperation model → FieldId → Bool
  | .document operation, field => operation.operationReferencesField field
  | .fixedString _ alternative, field => alternative.expression.core.referencesField field
  | .scalarCopy operation, field => operation.source.id == field
  | .firstFilled operation, field => operation.referencesWith field (·.referencesField field)
  | .stringExpression operation, field => operation.expression.referencesField field
  | .stringConstant _, _ | .booleanConstant _, _ | .fixedBooleanConstant _, _ => false
  | .enumeration operation, field => operation.source.referencesField field
  | .fixedEnumeration operation, field => operation.source.referencesField field
  | .dateRangeConstruction operation, field => operation.referencesField field
  | .temporalExpression operation, field => operation.expression.referencesField field
  | .dateLiteral _, _ => false

def referencesWith (operation : CheckedRowComputationOperation model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  match operation with
  | .document operation => operation.operationReferencesWith field filterReads
  | .firstFilled operation => operation.referencesWith field filterReads
  | .temporalExpression operation => operation.expression.referencesWith field filterReads
  | operation => operation.referencesField field

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
  | scalarCopy (cause : ScalarCopyFault)
  | firstFilled (cause : FirstFilledAlternativeFault)
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
  | .document operation => (operation.runSelected world patterns.targetMatcher? document).mapError .readBack
  | .fixedString table alternative => do
      let some matcher := patterns.targetMatcher? table.targetField
        | throw (.targetPatternUnavailable table.targetField)
      let context := document.stringComputationContext
      let store ← (alternative.expression.core.evaluate context).mapError .stringExpression
      let outcome ← ((table.toResolved .empty).targetRegime.check table.targetPolicy matcher store context).mapError .stringExpression
      pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)
  | .scalarCopy operation => (operation.evaluateAt document environment).mapError .scalarCopy
  | .firstFilled operation => (operation.evaluateAt world patterns document environment).mapError .firstFilled
  | .stringExpression operation =>
      let field := operation.targetField
      let some matcher := patterns.targetMatcher? field | throw (.targetPatternUnavailable field)
      let context := document.indexedComputationContextAt environment
      let result ← (operation.expression.eval .computation { read := context.read } context.numberText (some context)).mapError .stringExpression
      let term := StringTerm.ofOperand result
      let outcome ← (operation.target.checkStringExpressionTarget matcher term.store
        ((document.computationContextAt environment).withWorld world)).mapError .stringExpression
      pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)
  | .stringConstant operation =>
      let some matcher := patterns.targetMatcher? operation.checkedTarget.targetField
        | throw (.targetPatternUnavailable operation.checkedTarget.targetField)
      let outcome := operation.outcomeWithPattern matcher
      pure (.string outcome, ← (DocumentComputationReadBack.string outcome).mapError .readBack)
  | .booleanConstant operation => pure (booleanOutcome operation.operation.operation)
  | .fixedBooleanConstant operation => pure (booleanOutcome operation.operation.operation)
  | .temporalExpression operation =>
      let context := document.indexedComputationContextAt environment
      (operation.run (context.withWorld world)).mapError .readBack
  | .dateLiteral operation =>
      let outcome := operation.outcome
      let cell ← (DocumentComputationReadBack.dateConstant operation.dateTarget outcome).mapError .readBack
      pure (.fullDate outcome, cell)
  | .dateRangeConstruction operation =>
      let outcome ← (operation.evaluateWith (document.indexedComputationContextAt environment).read).mapError .dateRangeConstruction
      pure (.dateRange outcome, ← (DocumentComputationReadBack.dateRange model operation.target.policy outcome).mapError .readBack)
  | .enumeration operation =>
      let result ← (operation.evaluateAtWithRead document.read environment).mapError .enumeration
      let outcome := result.result.asExactStringTargetOutcome
      pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)
  | .fixedEnumeration operation =>
      let context := document.indexedComputationContextAt environment
      let outcome := (operation.source.evaluate { read := context.read }).asExactStringTargetOutcome
      pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)

end CheckedRowComputationOperation

namespace CheckedRowComputationTable

/-- A fixed document carrier contributes its checked guard and operation separately to the
same selector used by addressed alternatives (spec/09 §§1.1, 2). -/
def ofDocument? (step : CheckedDocumentComputationStep model) : Option (CheckedRowComputationTable model) :=
  (certifyRowComputationTable [{ operation := .document step, precondition := step.precondition.map (·.val) }]).toOption

/-- Separately admitted declarations concatenate after their own guardedness check; their
common conditions are already attached to each member (spec/09 §§1.1, 5). -/
def appendSameTarget? (left right : CheckedRowComputationTable model) :
    Option (CheckedRowComputationTable model) := do
  if target : right.target = left.target then
    if scope : right.scope = left.scope then
      if family : right.family = left.family then
        let members : List (CheckedRowComputationAlternative model left.target left.scope left.family) := by
          simpa only [target, scope, family] using (right.first :: right.remaining)
        pure { left with remaining := left.remaining ++ members }
      else none
    else none
  else none

/-- Fixed String expressions keep their original target regime and expression certificate when
a sibling declaration uses an addressed source at that same fixed target (spec/09 §5). -/
def ofString? (table : CheckedStringComputationTable model) : Option (CheckedRowComputationTable model) := do
  let first ← (certifyRowComputationTable [{
    operation := .fixedString table table.first
    precondition := table.first.precondition }]).toOption
  table.remaining.foldlM (fun combined alternative => do
    let next ← (certifyRowComputationTable [{
      operation := .fixedString table alternative
      precondition := alternative.precondition }]).toOption
    combined.appendSameTarget? next) first


def alternatives (table : CheckedRowComputationTable model) :=
  (table.first :: table.remaining).map (·.toResolved)

def operationReferencesWith (table : CheckedRowComputationTable model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  table.alternatives.any (·.operation.referencesWith field filterReads)

def operationReferencesField (table : CheckedRowComputationTable model) (field : FieldId) : Bool :=
  table.operationReferencesWith field (·.referencesField field)

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
      let context := (document.indexedComputationContextAt environment).withWorld world
      match CheckedComputationAlternative.selectFirstChecked table.alternatives context
          (some (document.resolveSemanticIndexColumnWith document.read)) with
      | .error error =>
          if error.isValueFailure then atRow environment (.valueError family) DocumentComputationReadBack.poison
          else throw (.guardBinding error)
      | .ok .noMatch => atRow environment family.noValue DocumentComputationReadBack.empty
      | .ok (.poison cause) => atRow environment (family.poison cause) DocumentComputationReadBack.poison
      | .ok (.selected operation) =>
          let (outcome, cell) ← operation.evaluateAt world patterns document environment
          atRow environment outcome cell)

end CheckedRowComputationTable
end A12Kernel
