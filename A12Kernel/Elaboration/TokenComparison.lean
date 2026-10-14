import A12Kernel.Elaboration.TokenFirstFilledValue

/-! # Checked comparisons of selected tokens

Both equality sides retain their literal, direct field, keyed field or first-filled source. Selection, empty
suppression and missing-prefix polarity stay with the existing token scan and symmetric comparison owners.
-/

namespace A12Kernel

inductive SurfaceTokenComparisonOperand where
  | literal (value : String)
  | field (reference : SurfaceFieldPath)
  | indexed (source : SurfaceSemanticIndex)
  | firstFilled (source : SurfaceFirstFilledTokenSource)

inductive TokenComparisonElabError where
  | model (error : ResolveError)
  | source (error : FirstFilledTokenElabError)
  | unsupportedSource
  | noFieldSource
  deriving Repr, DecidableEq

inductive CheckedTokenComparisonOperand (model : FlatModel) where
  | literal (value : String)
  | field (source : CheckedTokenField model)
  | firstFilled (source : CheckedFirstFilledTokenSource model)
      (supported : source.supportsCheckedFirstFilledValidation = true)
  /-- A keyed scalar read `[Field For key]`, kept apart from an authored `FirstFilledValue`. Its
  source is the selection alone: a direct read is the one-cell first-filled scan the `field` arm
  also evaluates, so selection, phase policy and partial coverage stay with the token scan
  (spec/08 §4.1). -/
  | indexed (source : CheckedFirstFilledTokenSource model)

namespace CheckedTokenComparisonOperand

def sources : CheckedTokenComparisonOperand model → List (CheckedFirstFilledTokenSource model)
  | .literal _ | .field _ => []
  | .firstFilled source _ | .indexed source => [source]

def evaluate (operand : CheckedTokenComparisonOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError (SimpleComparisonOperand String) :=
  match operand with
  | .literal value => pure (if value.isEmpty then .notEvaluated else .value value true)
  | .field source => do
      let cell ← document.fullValidationAddressedCell outer source.declaration.id
      pure ((evalFirstFilledToken {
        cells := [source.operand.checkedValueListCellAt .validation cell.cell]
        hasUninstantiatedTail := false, hasHaving := false }).asValidationOperand)
  | .firstFilled source supported =>
      FirstFilledTokenResult.asValidationOperand <$>
        source.evaluateSupportedFirstFilledValidation (world := world) document outer supported
  | .indexed source =>
      FirstFilledTokenResult.asValidationOperand <$>
        source.evaluateSupportedFirstFilledValidation (world := world) document outer rfl

def fields : CheckedTokenComparisonOperand model → List (CheckedTokenField model)
  | .field source => [source]
  | _ => []

def evaluatePartial? (operand : CheckedTokenComparisonOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError CheckedCell) :
    Option (Except CheckedAddressingError (Option (SimpleComparisonOperand String))) :=
  match operand with
  | .literal value => some (pure (some (if value.isEmpty then .notEvaluated else .value value true)))
  | .field source => some do
      if !scope.coversCell model source.declaration.path outer then return none
      let cell ← read outer source.declaration.id
      pure (some (evalFirstFilledToken {
        cells := [source.operand.checkedValueListCellAt .validation cell]
        hasUninstantiatedTail := false, hasHaving := false }).asValidationOperand)
  | .firstFilled source _ | .indexed source => do
      let result ← source.evaluateCheckedPartialFirstFilled? document outer scope read
      pure (result.map fun
        | .nonRelevant => none
        | .evaluated result => some result.asValidationOperand)

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
  | .field reference => do
      let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .model
      .field <$> ((certifyDirectTokenOperand model declaration).mapError fun cause => .source (.source cause))
  | .firstFilled authored => do
      let source ← (elaborateFirstFilledTokenSource model declaringGroup authored bindingGroup (some bindingGroup)).mapError .source
      if supported : source.supportsCheckedFirstFilledValidation = true then
        pure (.firstFilled source supported)
      else throw .unsupportedSource
  | .indexed authored =>
      .indexed <$> (elaborateTokenEntitySource model declaringGroup { first := .indexed authored .stored, rest := [] }
        (arity := .soleAllowed) (bindingGroup? := some bindingGroup)).mapError fun cause => .source (.source cause)

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
  (comparison.left.fields ++ comparison.right.fields).any (·.declaration.id == field) ||
    comparison.sources.any (·.referencesField field filterReads)

def bindingScopes (comparison : CheckedTokenComparison model) : List (List RepeatableLevel) :=
  (comparison.left.fields ++ comparison.right.fields).map (·.declaration.repeatableScope) ++
  comparison.sources.flatMap fun source => source.bindingScopes ++
    (source.operands.flatMap fun
      | .star source => source.filter.toList.flatMap fun filter =>
          (CorrelatedHaving.outerIterationScopes model filter.condition).filterMap id
      | _ => [])

def evaluateFull (comparison : CheckedTokenComparison model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) : Except CheckedAddressingError Verdict := do
  pure (comparison.operator.evalSymmetric (· == ·)
    (← comparison.left.evaluate (world := world) document outer) (← comparison.right.evaluate (world := world) document outer))

def evaluatePartial? (comparison : CheckedTokenComparison model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError CheckedCell) :
    Option (Except CheckedAddressingError Verdict) := do
  if comparison.hasHaving then none else pure ()
  let left ← comparison.left.evaluatePartial? document outer scope read
  let right ← comparison.right.evaluatePartial? document outer scope read
  let available := fun result => match result with
    | .error (.partialUnavailable _ _) => .ok none
    | result => result
  pure do
    let left ← available left
    let right ← available right
    pure (match left, right with
      | some left, some right => comparison.operator.evalSymmetric (· == ·) left right
      | _, _ => .unknown)

end CheckedTokenComparison
end A12Kernel
