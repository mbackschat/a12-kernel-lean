import A12Kernel.Elaboration.HavingSelectedComparison
import A12Kernel.Elaboration.StringComputation

namespace A12Kernel

private def sourceAdmitted (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (source : HavingStringSource) : Bool :=
  source.presenceSlots.all (·.wellFormedForEnvironments model candidateLevels outerLevels) &&
    match source with
    | .field _ => true
    | .firstFilled slots =>
      (HavingSelectedOperand.firstFilled slots).wellFormed model candidateLevels outerLevels &&
        slots.all fun slot => slot.references.all fun
          | .text ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
              match ref.operand with
              | .string _ => (admitStringExpressionField declaration).isOk
              | .enumeration operand => match operand.projection with
                  | .stored => (admitStringExpressionField declaration).isOk
                  | .category _ => true
          | _ => false

private def expressionAdmitted (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (allowStoredEnumeration : Bool := false) : StringExpr HavingStringSource → Bool
  | .literal _ => true
  | .concat left right => expressionAdmitted model candidateLevels outerLevels false left &&
      expressionAdmitted model candidateLevels outerLevels false right
  | expression =>
      expression.fields.all (sourceAdmitted model candidateLevels outerLevels) &&
      match expression with
      | .field (.firstFilled _) => true
      | .field (.field ref) => (model.lookupUniqueId ref.field).toOption.any fun declaration =>
          declaration.fieldValueReadRefusal?.isNone && ((admitStringExpressionField declaration).isOk ||
            (allowStoredEnumeration && (declaration.toEnumerationTextFieldComparison? .stored).isSome))
      | .category (.field ref) projection => (model.lookupUniqueId ref.field).toOption.any fun declaration =>
          declaration.enumeration.any fun enumeration =>
            enumeration.categories.any fun category => stringCategory? declaration category.name == some projection
      | .fieldValueAsString (.field ref) => (model.lookupUniqueId ref.field).toOption.any fun declaration =>
          (admitNumberAsStringField declaration).isOk
      | .range (.field ref) start finish => validStringRange start finish &&
          (model.lookupUniqueId ref.field).toOption.any fun declaration => (admitStringComputationValueField declaration).isOk
      | _ => false

private def operandsAdmitted (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (left right : StringExpr HavingStringSource) : Bool :=
  let isCategory : StringExpr HavingStringSource → Bool | .category .. => true | _ => false
  expressionAdmitted model candidateLevels outerLevels (isCategory right) left &&
    expressionAdmitted model candidateLevels outerLevels (isCategory left) right

/-- `CheckOpUtils.isConstant` classifies authored literals and their braces, not expressions
without field dependencies. String lowering erases braces but retains concatenation nodes. -/
private def stringComparisonEntry : StringExpr HavingStringSource → ComparisonEntryOperand
  | .literal _ => .literal .string
  | _ => .expression .string

def HavingStringComparison.wellFormed (source : HavingStringComparison) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  operandsAdmitted model candidateLevels outerLevels source.left source.right &&
    comparisonConstantPairAllowed (stringComparisonEntry source.left) (stringComparisonEntry source.right) &&
    match source.left, source.right with
    | .category _ projection, .literal text | .literal text, .category _ projection => projection.categoryTokens.contains text
    | _, _ => true

/-- Reuse the ordinary declaration gates; source resolution keeps each authored occurrence's
candidate/captured environment and the operator's field-value versus entity read class. -/
def elaborateHavingStringComparison (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel)
    (resolve : SurfaceHavingStringRef → Bool → Except CorrelationElabError FlatFieldDecl)
    (operator : SurfaceComparisonOp) (left right : StringExpr SurfaceHavingSelectedOperand String) :
    Except CorrelationElabError HavingStringComparison := do
  let direct (source : SurfaceHavingSelectedOperand) (valueRead : Bool) := do
    let .field ref := source | throw CorrelationElabError.numericExpressionUnsupported
    let declaration ← resolve ref valueRead
    pure (ref, declaration)
  let rec expression : StringExpr SurfaceHavingSelectedOperand String → Except CorrelationElabError (StringExpr HavingStringSource)
    | .literal text => pure (.literal text)
    | .concat left right => return .concat (← expression left) (← expression right)
    | .field (.firstFilled source) => do
        let slots ← resolveHavingProjectedEntityList model declaringGroup candidateLevels outerLevels source
        return .field (.firstFilled (← slots.mapM (·.mapM resolveHavingSelectedReference)))
    | .field source => do
        let (ref, declaration) ← direct source true
        pure (.field (.field { origin := ref.origin, field := declaration.id }))
    | .category source name => do
        let .field ref := source | throw .numericExpressionUnsupported
        let declaration ← resolve { ref with projectionRef := .category name } true
        let some projection := stringCategory? declaration name | throw .numericExpressionUnsupported
        pure (.category (.field { origin := ref.origin, field := declaration.id }) projection)
    | .fieldValueAsString source => do
        let (ref, declaration) ← direct source false
        pure (.fieldValueAsString (.field { origin := ref.origin, field := declaration.id }))
    | .range source start finish => do
        let (ref, declaration) ← direct source false
        pure (.range (.field { origin := ref.origin, field := declaration.id }) start finish)
  let first ← expression left
  let second ← expression right
  if !operandsAdmitted model candidateLevels outerLevels first second then throw .numericExpressionUnsupported
  discard <| (checkComparisonEntry (if operator.toEquality?.isSome then .equality else .ordering)
    (stringComparisonEntry first) (stringComparisonEntry second)).mapError .comparisonEntry
  let some equality := operator.toEquality? | throw .incoherentCore
  let result : HavingStringComparison := { operator := equality, left := first, right := second }
  if !result.wellFormed model candidateLevels outerLevels then throw .numericExpressionUnsupported
  pure result

end A12Kernel
