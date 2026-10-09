import A12Kernel.Elaboration.HavingSelectedComparison
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.ScalarComparisonAdmission

namespace A12Kernel

/-- A selector contributes a String result; the immediate-field display restriction does not
propagate into its selected declarations (CheckOperationImpl.checkWithoutDisplayValues). -/
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
              | .string _ => (admitStringExpressionField declaration true).isOk
              | .enumeration operand => match operand.projection with
                  | .stored => (admitStringExpressionField declaration true).isOk
                  | .category _ => true
          | _ => false

private def expressionAdmitted (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (allowStoredEnumeration : Bool := false) : StringExpr HavingStringSource → Bool
  | .literal _ => true
  | .group body => expressionAdmitted model candidateLevels outerLevels true body
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
  expressionAdmitted model candidateLevels outerLevels true left &&
    expressionAdmitted model candidateLevels outerLevels true right

private def comparisonOperand (model : FlatModel) :
    StringExpr HavingStringSource → Option ScalarComparisonOperand
  | .literal text => some { type := .stringLike, literal := some (.inl text) }
  | .group source => (comparisonOperand model source).map fun operand => { operand with directField := false }
  | .field (.field ref) => (model.lookupUniqueId ref.field).toOption.map fun declaration =>
      { type := NumericOperandType.ofDeclaration declaration, directField := true }
  | .category _ projection => some { type := .enumeration .category projection.categoryTokens, directField := true }
  | _ => some { type := .stringLike }

/-- `CheckOpUtils.isConstant` classifies authored literals and their braces, not expressions
without field dependencies. Retained braces preserve this classification through admission. -/
private def stringComparisonEntry : StringExpr HavingStringSource → ComparisonEntryOperand
  | .literal _ => .literal .string
  | .group body => .grouped (stringComparisonEntry body)
  | _ => .expression .string

def HavingStringComparison.wellFormed (source : HavingStringComparison) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  operandsAdmitted model candidateLevels outerLevels source.left source.right &&
    comparisonConstantPairAllowed (stringComparisonEntry source.left) (stringComparisonEntry source.right) &&
    (comparisonOperand model source.left).any fun left =>
      (comparisonOperand model source.right).any fun right =>
        (checkScalarComparison (if source.operator == .equal then .equal else .notEqual) left right).toOption == some true

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
    | .group body => .group <$> expression body
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
  let some leftOperand := comparisonOperand model first | throw .incoherentCore
  let some rightOperand := comparisonOperand model second | throw .incoherentCore
  discard <| (checkScalarComparison operator leftOperand rightOperand).mapError .comparisonEntry
  let result : HavingStringComparison := { operator := equality, left := first, right := second }
  if !result.wellFormed model candidateLevels outerLevels then throw .numericExpressionUnsupported
  pure result

end A12Kernel
