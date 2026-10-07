import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.CheckedStarDocument

namespace A12Kernel

namespace StringExpr

def fields : StringExpr Atom Category → List Atom
  | .field fieldId | .category fieldId _ | .fieldValueAsString fieldId | .range fieldId _ _ => [fieldId]
  | .literal _ => []
  | .concat left right => left.fields ++ right.fields

end StringExpr

abbrev SurfaceSelectedStringExpression := StringExpr (Sum SurfaceFieldPath SurfaceSemanticIndex) String
abbrev ResolvedStringSource (model : FlatModel) := Sum FieldId (CheckedSemanticIndexSource model)

private def stringSourceField : ResolvedStringSource model → FieldId
  | .inl field => field
  | .inr source => source.targetDeclaration.id

private def stringSourceBoundFields : ResolvedStringSource model → List FieldId
  | .inl field => [field]
  | .inr source => match source.key with | .field key => [key.id] | .literal .. => []

/-- The common String tree retains ordinary field identities and complete checked selections. -/
structure CheckedBoundStringExpression (model : FlatModel) where
  private mk ::
  core : StringExpr (ResolvedStringSource model)
  declarations : List FlatFieldDecl
  boundDeclarations : List FlatFieldDecl
  scope : List RepeatableLevel
  modelWellFormed : model.validate.isOk = true

def CheckedBoundStringExpression.bindingScopes (source : CheckedBoundStringExpression model) :
    List (List RepeatableLevel) :=
  source.boundDeclarations.map (·.repeatableScope) ++ source.core.fields.flatMap fun
    | .inl _ => []
    | .inr selection => selection.bindingScopes

private def certifyBoundStringExpression (model : FlatModel) (rowGroup : GroupPath)
    (core : StringExpr (ResolvedStringSource model)) :
    Except StringComputationElabError (CheckedBoundStringExpression model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      let fields := core.fields.flatMap fun
        | .inl field => [field]
        | .inr source => (model.fields.filter fun field => source.referencesField field.id).map (·.id)
      let declarations ← fields.mapM fun field => (model.lookupUniqueId field).mapError .resolve
      let boundDeclarations ← (core.fields.flatMap stringSourceBoundFields).mapM fun field =>
        (model.lookupUniqueId field).mapError .resolve
      let scope := model.repeatableScopeForGroupPath rowGroup
      let checked : CheckedBoundStringExpression model :=
        { core, declarations, boundDeclarations, scope, modelWellFormed := by rw [hModel]; rfl }
      if !checked.bindingScopes.all (·.isPrefixOf scope) then throw .incoherentCore
      pure checked

private def elaborateSelectedStringCore (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (expression : SurfaceSelectedStringExpression) (categoryComparison : Bool := false) :
    Except StringComputationElabError (StringExpr (ResolvedStringSource model)) := do
  let direct (source : StringExpr SurfaceFieldPath String) :=
    (·.mapSources Sum.inl) <$> elaborateStringExprCore model declaringGroup rowGroup source
  let selected source := (elaborateSemanticIndexSource model declaringGroup source
    (some (model.repeatableScopeForGroupPath rowGroup))).mapError StringComputationElabError.indexed
  let admitField (declaration : FlatFieldDecl) :=
    if categoryComparison && (declaration.toEnumerationTextFieldComparison? .stored).isSome then
      pure declaration.id
    else admitStringExpressionField declaration
  match expression with
  | .field (.inl path) => do
      let declaration ← (model.resolveComputationFieldValueRead declaringGroup rowGroup path).mapError .resolve
      pure (.field (.inl (← admitField declaration)))
  | .category (.inl path) name => direct (.category path name)
  | .fieldValueAsString (.inl path) => direct (.fieldValueAsString path)
  | .range (.inl path) start finish => direct (.range path start finish)
  | .literal text => pure (.literal text)
  | .field (.inr authored) =>
      let source ← selected authored
      if let some error := source.targetDeclaration.fieldValueReadRefusal? then throw (.resolve error)
      discard <| admitField source.targetDeclaration
      pure (.field (.inr source))
  | .category (.inr authored) name =>
      let source ← selected authored
      let some projection := stringCategory? source.targetDeclaration name | throw .incoherentCore
      pure (.category (.inr source) projection)
  | .range (.inr authored) start finish =>
      let source ← selected authored
      if !validStringRange start finish then throw (.invalidRange start finish)
      discard <| admitStringComputationValueField source.targetDeclaration
      pure (.range (.inr source) start finish)
  | .fieldValueAsString (.inr authored) => do
      let source ← selected authored
      discard <| admitNumberAsStringField source.targetDeclaration
      pure (.fieldValueAsString (.inr source))
  | .concat left right => pure (.concat
      (← elaborateSelectedStringCore model declaringGroup rowGroup left)
      (← elaborateSelectedStringCore model declaringGroup rowGroup right))

/-- Ordinary and selected leaves share the target's free row scope; the selector owns its target row. -/
def elaborateSelectedBoundStringExpression (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (expression : SurfaceSelectedStringExpression) :
    Except StringComputationElabError (CheckedBoundStringExpression model) := do
  discard <| model.validate.mapError StringComputationElabError.resolve
  certifyBoundStringExpression model rowGroup (← elaborateSelectedStringCore model declaringGroup rowGroup expression)

def elaborateBoundStringExpression (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (expression : StringExpr SurfaceFieldPath String) :
    Except StringComputationElabError (CheckedBoundStringExpression model) :=
  elaborateSelectedBoundStringExpression model declaringGroup rowGroup (expression.mapSources Sum.inl)

namespace CheckedBoundStringExpression

def referencesField (expression : CheckedBoundStringExpression model) (field : FieldId) : Bool :=
  expression.declarations.any (·.id == field)

def hasIndexed (expression : CheckedBoundStringExpression model) : Bool :=
  expression.core.fields.any fun | .inr _ => true | .inl _ => false

/-- Number coercion consumes the document's selected formal-read text. A missing text for a present
Number is a context fault, never a guessed rendering or a fabricated formal cause. -/
def eval (expression : CheckedBoundStringExpression model) (phase : Phase)
    (context : FlatContext) (numberText : FieldId → Option String)
    (selected : Option ScalarComputationContext := none) :
    Except StringComputationFault (SimpleComparisonOperand String) :=
  expression.core.evalOperandWithSource stringSourceField phase fun source => do
    match source with
    | .inr source =>
        let some context := selected | throw .indexedReadUnavailable
        let observation ← (source.observeColumnWith phase context.semanticIndexColumnReader
          context.row context.read context.storedText).mapError (fun _ => .indexedReadUnavailable)
        match source.targetDeclaration.policy.kind with
        | .number _ =>
            match observation with
            | .empty => pure .notEvaluated
            | .unknown cause | .poison cause => pure (.unknown cause)
            | .value (.num _) =>
                let some addressed := context.addressed | throw .indexedReadUnavailable
                let .value environment ← (source.selectEnvironmentWith phase context.semanticIndexColumnReader
                  context.row context.read context.storedText).mapError (fun _ => .indexedReadUnavailable)
                  | throw .indexedReadUnavailable
                let some text := addressed.numberText environment source.targetDeclaration.id
                  | throw .indexedReadUnavailable
                pure (.value text true)
            | .value _ => throw (.fieldKindMismatch source.targetDeclaration.id)
        | _ => StringExpr.readObservedOperand source.targetDeclaration.id observation
    | .inl field =>
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

def elaborateSelectedStringExpressionComparison (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (operator : EqualityOp) (left right : SurfaceSelectedStringExpression) :
    Except StringComputationElabError (CheckedStringExpressionComparison model) := do
  discard <| model.validate.mapError StringComputationElabError.resolve
  let isCategory : SurfaceSelectedStringExpression → Bool
    | .category .. => true
    | _ => false
  -- spec/06 §B.1 gives direct category comparisons a separate domain/display gate;
  -- the bypass does not propagate into concatenation or other expression nodes.
  let resolvedLeft ← elaborateSelectedStringCore model declaringGroup rowGroup left (isCategory right)
  let resolvedRight ← elaborateSelectedStringCore model declaringGroup rowGroup right (isCategory left)
  let validLiteral : StringExpr (ResolvedStringSource model) → StringExpr (ResolvedStringSource model) → Bool
    | .category _ projection, .literal text | .literal text, .category _ projection =>
        projection.categoryTokens.contains text
    | _, _ => true
  if !validLiteral resolvedLeft resolvedRight then throw .incoherentCore
  pure { left := ← certifyBoundStringExpression model rowGroup resolvedLeft
         right := ← certifyBoundStringExpression model rowGroup resolvedRight, operator }

namespace CheckedStringExpressionComparison

def declarations (comparison : CheckedStringExpressionComparison model) : List FlatFieldDecl :=
  comparison.left.declarations ++ comparison.right.declarations

def boundDeclarations (comparison : CheckedStringExpressionComparison model) : List FlatFieldDecl :=
  comparison.left.boundDeclarations ++ comparison.right.boundDeclarations

def bindingScopes (comparison : CheckedStringExpressionComparison model) : List (List RepeatableLevel) :=
  comparison.left.bindingScopes ++ comparison.right.bindingScopes

def hasIndexed (comparison : CheckedStringExpressionComparison model) : Bool :=
  comparison.left.hasIndexed || comparison.right.hasIndexed

def referencesField (comparison : CheckedStringExpressionComparison model) (field : FieldId) : Bool :=
  comparison.left.referencesField field || comparison.right.referencesField field

private def operand (expression : CheckedBoundStringExpression model) (phase : Phase)
    (context : FlatContext) (numberText : FieldId → Option String)
    (selected : Option ScalarComputationContext) :
    Except StringComputationFault (SimpleComparisonOperand String) := do
  let result ← expression.eval phase context numberText selected
  match result with
  | .value text _ => if text.isEmpty then pure .notEvaluated else pure result
  | _ => pure result

def eval (comparison : CheckedStringExpressionComparison model) (context : FlatContext)
    (numberText : FieldId → Option String) (selected : Option ScalarComputationContext := none) : Except StringComputationFault Verdict := do
  let left ← operand comparison.left .validation context numberText selected
  let right ← operand comparison.right .validation context numberText selected
  pure (evalSymmetricComparison (fun a b => comparison.operator.holds (a == b)) left right)

def evalComputation (comparison : CheckedStringExpressionComparison model) (context : FlatContext)
    (numberText : FieldId → Option String) (selected : Option ScalarComputationContext := none) : Except StringComputationFault ComputationConditionResult :=
  evalComputationComparisonExcept (fun a b => comparison.operator.holds (a == b))
    (operand comparison.left .computation context numberText selected)
    (fun _ => operand comparison.right .computation context numberText selected)

end CheckedStringExpressionComparison

/-- Each target instance and its expression share one free row binding and source set. -/
structure CheckedRowStringExpression (model : FlatModel) where
  private mk ::
  targetField : FieldId
  target : FlatFieldDecl
  targetOwned : model.lookupUniqueId targetField = .ok target
  expression : CheckedBoundStringExpression model

inductive RowStringExpressionElabError where
  | target (error : AddressedRepeatableTargetElabError)
  | expression (error : StringComputationElabError)
  | targetKind
  | selfReference
  deriving Repr, DecidableEq

def elaborateSelectedRowStringExpression (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (surface : SurfaceSelectedStringExpression) :
    Except RowStringExpressionElabError (CheckedRowStringExpression model) := do
  match owned : model.lookupUniqueId targetField with
  | .error error => throw (.target (.target error))
  | .ok target =>
      if !GroupPath.isValid declaringGroup then throw (.target (.target (.invalidRuleGroup declaringGroup)))
      if !target.repeatableScope.isEmpty then
        discard <| (checkAddressedRepeatableTarget model declaringGroup targetField).mapError .target
      if !target.isStringExpressionTarget then throw .targetKind
      let expression ← (elaborateSelectedBoundStringExpression model declaringGroup target.groupPath surface).mapError .expression
      if expression.referencesField targetField then throw .selfReference
      pure { targetField, target, targetOwned := owned, expression }

def elaborateRowStringExpression (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (surface : StringExpr SurfaceFieldPath String) :
    Except RowStringExpressionElabError (CheckedRowStringExpression model) :=
  elaborateSelectedRowStringExpression model declaringGroup targetField (surface.mapSources Sum.inl)

end A12Kernel
