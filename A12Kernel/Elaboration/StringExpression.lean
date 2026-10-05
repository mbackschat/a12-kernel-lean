import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.Flat.FieldValueRead

namespace A12Kernel

namespace StringExpr

def fields : StringExpr FieldId → List FieldId
  | .field fieldId | .category fieldId _ | .fieldValueAsString fieldId | .range fieldId _ _ => [fieldId]
  | .literal _ => []
  | .concat left right => left.fields ++ right.fields

end StringExpr

/-- The existing String tree bound at one row scope. Every leaf retains its model declaration;
root and row consumers differ only in the environment used to read those declarations. -/
structure CheckedBoundStringExpression (model : FlatModel) where
  private mk ::
  core : StringExpr FieldId
  declarations : List FlatFieldDecl
  scope : List RepeatableLevel
  modelWellFormed : model.validate.isOk = true

/-- Reuse the String constructor/kind gates before certifying the consumer's complete row binding. -/
def elaborateBoundStringExpression (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (expression : StringExpr SurfaceFieldPath String) :
    Except StringComputationElabError (CheckedBoundStringExpression model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      let core ← elaborateStringExprCore model declaringGroup rowGroup expression
      let declarations ← core.fields.mapM fun field => (model.lookupUniqueId field).mapError .resolve
      let scope := model.repeatableScopeForGroupPath rowGroup
      if !(declarations.all fun field => field.repeatableScope.isPrefixOf scope) then throw .incoherentCore
      pure { core, declarations, scope, modelWellFormed := by rw [hModel]; rfl }

namespace CheckedBoundStringExpression

def referencesField (expression : CheckedBoundStringExpression model) (field : FieldId) : Bool :=
  expression.core.referencesField field

/-- Number coercion consumes the document's selected formal-read text. A missing text for a present
Number is a context fault, never a guessed rendering or a fabricated formal cause. -/
def eval (expression : CheckedBoundStringExpression model) (phase : Phase)
    (context : FlatContext) (numberText : FieldId → Option String) :
    Except StringComputationFault (SimpleComparisonOperand String) :=
  expression.core.evalOperandWith phase fun field => do
    let cell := context.read field
    let number := expression.declarations.any fun declaration =>
      declaration.id == field && match declaration.policy.kind with | .number _ => true | _ => false
    if number then
      match observeCell phase cell with
      | .empty => pure .notEvaluated
      | .unknown cause | .poison cause => pure (.unknown cause)
      | .value (.num _) => match numberText field with
          | some text => pure (.value text true)
          | none => throw (.fieldKindMismatch field)
      | .value _ => throw (.fieldKindMismatch field)
    else StringExpr.readOperandAt phase context.read field

end CheckedBoundStringExpression

/-- String equality uses the same expression result as storage, but a computed empty result cannot
participate in a comparison, including an empty literal (String grid, 2026-10-04). -/
structure CheckedStringExpressionComparison (model : FlatModel) where
  left : CheckedBoundStringExpression model
  right : CheckedBoundStringExpression model
  operator : EqualityOp

def elaborateStringExpressionComparison (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (operator : EqualityOp) (left right : StringExpr SurfaceFieldPath String) :
    Except StringComputationElabError (CheckedStringExpressionComparison model) := do
  pure { left := ← elaborateBoundStringExpression model declaringGroup rowGroup left
         right := ← elaborateBoundStringExpression model declaringGroup rowGroup right
         operator }

namespace CheckedStringExpressionComparison

def declarations (comparison : CheckedStringExpressionComparison model) : List FlatFieldDecl :=
  comparison.left.declarations ++ comparison.right.declarations

def referencesField (comparison : CheckedStringExpressionComparison model) (field : FieldId) : Bool :=
  comparison.left.referencesField field || comparison.right.referencesField field

private def operand (expression : CheckedBoundStringExpression model) (phase : Phase)
    (context : FlatContext) (numberText : FieldId → Option String) :
    Except StringComputationFault (SimpleComparisonOperand String) := do
  let result ← expression.eval phase context numberText
  match result with
  | .value text _ => if text.isEmpty then pure .notEvaluated else pure result
  | _ => pure result

def eval (comparison : CheckedStringExpressionComparison model) (context : FlatContext)
    (numberText : FieldId → Option String) : Except StringComputationFault Verdict := do
  let left ← operand comparison.left .validation context numberText
  let right ← operand comparison.right .validation context numberText
  pure (evalSymmetricComparison (fun a b => comparison.operator.holds (a == b)) left right)

def evalComputation (comparison : CheckedStringExpressionComparison model) (context : FlatContext)
    (numberText : FieldId → Option String) : Except StringComputationFault ComputationConditionResult :=
  evalComputationComparisonExcept (fun a b => comparison.operator.holds (a == b))
    (operand comparison.left .computation context numberText)
    (fun _ => operand comparison.right .computation context numberText)

end CheckedStringExpressionComparison

/-- A row target and its complete String expression share one environment binding and source set. -/
structure CheckedRowStringExpression (model : FlatModel) where
  private mk ::
  target : CheckedAddressedRepeatableTarget model
  expression : CheckedBoundStringExpression model

inductive RowStringExpressionElabError where
  | target (error : AddressedRepeatableTargetElabError)
  | expression (error : StringComputationElabError)
  | targetKind
  | selfReference
  deriving Repr, DecidableEq

def elaborateRowStringExpression (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (surface : StringExpr SurfaceFieldPath String) :
    Except RowStringExpressionElabError (CheckedRowStringExpression model) := do
  let target ← (checkAddressedRepeatableTarget model declaringGroup targetField).mapError .target
  if !target.declaration.isStringExpressionTarget then throw .targetKind
  let expression ← (elaborateBoundStringExpression model declaringGroup target.declaration.groupPath surface).mapError .expression
  if expression.referencesField targetField then throw .selfReference
  pure { target, expression }

end A12Kernel
