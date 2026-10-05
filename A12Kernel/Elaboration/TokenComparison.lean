import A12Kernel.Elaboration.TokenFirstFilledValue

/-! # Checked comparisons of selected tokens

Both equality sides retain their literal or first-filled source. Selection, empty suppression and
missing-prefix polarity stay with the existing token scan and symmetric comparison owners.
-/

namespace A12Kernel

inductive SurfaceTokenComparisonOperand where
  | literal (value : String)
  | firstFilled (source : SurfaceFirstFilledTokenSource)

inductive TokenComparisonElabError where
  | model (error : ResolveError)
  | source (error : FirstFilledTokenElabError)
  | unsupportedSource
  | noFieldSource
  deriving Repr

inductive CheckedTokenComparisonOperand (model : FlatModel) where
  | literal (value : String)
  | firstFilled (source : CheckedFirstFilledTokenSource model)
      (supported : source.supportsCheckedFirstFilledValidation = true)

namespace CheckedTokenComparisonOperand

def sources : CheckedTokenComparisonOperand model → List (CheckedFirstFilledTokenSource model)
  | .literal _ => []
  | .firstFilled source _ => [source]

def evaluate (operand : CheckedTokenComparisonOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (SimpleComparisonOperand String) :=
  match operand with
  | .literal value => pure (if value.isEmpty then .notEvaluated else .value value true)
  | .firstFilled source supported =>
      FirstFilledTokenResult.asValidationOperand <$>
        source.evaluateSupportedFirstFilledValidation document outer supported

end CheckedTokenComparisonOperand

/-- The sealed comparison contains only sources supported by its checked-document evaluator. -/
structure CheckedTokenComparison (model : FlatModel) where
  private mk ::
  left : CheckedTokenComparisonOperand model
  right : CheckedTokenComparisonOperand model
  operator : EqualityOp
  modelWellFormed : model.validate.isOk = true

private def resolveTokenComparisonOperand (model : FlatModel) (declaringGroup bindingGroup : GroupPath) :
    SurfaceTokenComparisonOperand → Except TokenComparisonElabError (CheckedTokenComparisonOperand model)
  | .literal value => pure (.literal value)
  | .firstFilled authored => do
      let source ← (elaborateFirstFilledTokenSource model declaringGroup authored bindingGroup (some bindingGroup)).mapError .source
      if supported : source.supportsCheckedFirstFilledValidation = true then
        pure (.firstFilled source supported)
      else throw .unsupportedSource

def elaborateTokenComparison (model : FlatModel) (declaringGroup : GroupPath)
    (operator : EqualityOp) (left right : SurfaceTokenComparisonOperand)
    (bindingGroup : GroupPath := declaringGroup) :
    Except TokenComparisonElabError (CheckedTokenComparison model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let left ← resolveTokenComparisonOperand model declaringGroup bindingGroup left
      let right ← resolveTokenComparisonOperand model declaringGroup bindingGroup right
      if (left.sources ++ right.sources).isEmpty then throw .noFieldSource
      pure { left, right, operator, modelWellFormed := by rw [h]; rfl }

namespace CheckedTokenComparison

def sources (comparison : CheckedTokenComparison model) : List (CheckedFirstFilledTokenSource model) :=
  comparison.left.sources ++ comparison.right.sources

def hasHaving (comparison : CheckedTokenComparison model) : Bool :=
  comparison.sources.any (·.hasHaving)

def referencesField (comparison : CheckedTokenComparison model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  comparison.sources.any (·.referencesField field filterReads)

def bindingScopes (comparison : CheckedTokenComparison model) : List (List RepeatableLevel) :=
  comparison.sources.flatMap fun source => source.bindingScopes ++
    (source.operands.flatMap fun
      | .star source => source.filter.toList.flatMap fun filter =>
          (CorrelatedHaving.outerIterationScopes model filter.condition).filterMap id
      | _ => [])

def evaluateFull (comparison : CheckedTokenComparison model)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError Verdict := do
  pure (comparison.operator.evalSymmetric (· == ·)
    (← comparison.left.evaluate document outer) (← comparison.right.evaluate document outer))

end CheckedTokenComparison
end A12Kernel
