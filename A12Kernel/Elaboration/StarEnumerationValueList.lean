import A12Kernel.Elaboration.Correlation
import A12Kernel.Semantics.EnumerationValueList

/-! # Checked nested Enumeration-star literal value lists

This capsule admits one general starred ordinary closed Enumeration field against a nonempty literal token list, with an optional checked `Having`. The selected stored/category projection supplies both static literal admission and runtime token classification; topology, filtering, partial relevance, and quantifier behavior remain with their shared owners.
-/

namespace A12Kernel

/-- One parser-independent starred Enumeration-fields/literal-values source. -/
structure SurfaceStarEnumerationValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceStarFieldPath
  projectionRef : EnumerationProjectionRef := .stored
  values : List String
  having : Option SurfaceCorrelatedHaving := none
  deriving Repr, DecidableEq

/-- One general starred field path certified as an exact checked Enumeration projection. -/
structure CheckedStarEnumerationSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  operand : CheckedEnumerationValueListOperand
  fieldOwned : source.declaration.policy.kind = .enumeration
  enumerationOwned : source.declaration.enumeration = some operand.declaration.declaration
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)

/-- A checked nested Enumeration star and its nonempty, projection-admitted literal side. -/
structure CheckedStarEnumerationValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  fields : CheckedStarEnumerationSource model
  firstValue : String
  restValues : List String
  literalsAllowed :
    (firstValue :: restValues).all
      (fields.operand.declaration.literalAllowed fields.operand.projection) = true

inductive StarEnumerationValueListElabError where
  | path (error : StarPathElabError)
  | fieldNotEnumeration (path : List String) (actual : SurfaceScalarKind)
  | enumerationOperand (path : List String) (error : EnumerationOperandError)
  | having (error : CorrelationElabError)
  | emptyValues
  | incoherentCore
  deriving Repr, DecidableEq

private theorem elaborateEnumeration_declaration_exact
    (source : EnumerationDeclaration) (checked : CheckedEnumerationDeclaration)
    (elaborated : elaborateEnumeration source = .ok checked) :
    checked.declaration = source := by
  unfold elaborateEnumeration at elaborated
  split at elaborated
  · cases elaborated
    rfl
  · contradiction

/-- Reuse the general checked star path, then retain its exact checked stored/category projection. -/
def elaborateStarEnumerationSource (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceStarFieldPath) (projectionRef : EnumerationProjectionRef)
    (having : Option SurfaceCorrelatedHaving := none) :
    Except StarEnumerationValueListElabError
      (CheckedStarEnumerationSource model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored |>.mapError .path
  match hKind : source.declaration.policy.kind,
      hEnumeration : source.declaration.enumeration with
  | .enumeration, some declaration =>
      match hChecked : elaborateEnumeration declaration with
      | .error _ => throw .incoherentCore
      | .ok checked =>
          match hProjection : checked.resolveProjection projectionRef with
          | .error error =>
              throw (.enumerationOperand source.declaration.path error)
          | .ok projection =>
              let operand : CheckedEnumerationValueListOperand := {
                declaration := checked
                projectionRef
                projection
                projectionChecked := hProjection }
              let filter ← match having with
                | none => pure none
                | some authoredFilter =>
                    pure (some (← elaborateStarHavingCore model declaringGroup source
                      authoredFilter |>.mapError .having))
              pure {
                source
                operand
                fieldOwned := hKind
                enumerationOwned := by
                  rw [elaborateEnumeration_declaration_exact declaration checked hChecked]
                  exact hEnumeration
                declaringGroup
                filter }
  | actual, _ =>
      throw (.fieldNotEnumeration source.declaration.path actual.surfaceKind)

/-- Check projection-specific literal admission after the exact starred Enumeration operand has been resolved. -/
def elaborateStarEnumerationValueListSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceStarEnumerationValueListSource) :
    Except StarEnumerationValueListElabError
      (CheckedStarEnumerationValueListSource model) := do
  let fields ← elaborateStarEnumerationSource model declaringGroup authored.fields
    authored.projectionRef authored.having
  match authored.values with
  | [] => throw .emptyValues
  | firstValue :: restValues =>
      let values := firstValue :: restValues
      if hAllowed : values.all
          (fields.operand.declaration.literalAllowed fields.operand.projection) = true then
        pure {
          quantifier := authored.quantifier
          fields := fields
          firstValue := firstValue
          restValues := restValues
          literalsAllowed := hAllowed }
      else
        match values.find? fun value =>
            !fields.operand.declaration.literalAllowed fields.operand.projection value with
        | some value =>
            throw (.enumerationOperand fields.source.declaration.path (.invalidLiteral value))
        | none => throw .incoherentCore

namespace CheckedStarEnumerationSource

/-- Classify one resolved leaf through the exact declaration-owned check and selected stored/category projection. -/
def valueListCell (checked : CheckedStarEnumerationSource model)
    (read : Env → FieldId → RawCell) (environment : Env) : ValueListCell .token :=
  checked.operand.projection.asValueListCell
    (observeCell .validation (checked.source.checkedCell read environment))

/-- Resolve nested topology once, optionally filter before projection, and retain hierarchical omitted-tail state. -/
def resolvedValueSide (checked : CheckedStarEnumerationSource model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide document outer
    checked.filter filterRead (checked.valueListCell read)

/-- Resolve partial relevance before reading or projecting retained Enumeration cells. -/
def resolvedPartialValueSide (checked : CheckedStarEnumerationSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError (ResolvedValueListQuantifierSide .token) :=
  checked.source.resolvedPartialValueListSide document outer scope
    (checked.valueListCell read)

end CheckedStarEnumerationSource

namespace CheckedStarEnumerationValueListSource

def values (checked : CheckedStarEnumerationValueListSource model) : List String :=
  checked.firstValue :: checked.restValues

def resolvedValuesSide (checked : CheckedStarEnumerationValueListSource model) :
    ResolvedValueListSide .token :=
  literalTokenValueListSide checked.values

/-- Evaluate full validation through the shared checked-star and token-list boundaries. -/
def evaluateFull (checked : CheckedStarEnumerationValueListSource model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) : Except StarAddressingError Verdict := do
  let fields ← checked.fields.resolvedValueSide document outer filterRead read
  pure (checked.quantifier.eval fields checked.resolvedValuesSide)

/-- Skip a filtered rule before topology or reads; otherwise classify partial relevance per expanded cell. -/
def evaluatePartial (checked : CheckedStarEnumerationValueListSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialHavingValueListResult :=
  if hUnfiltered : checked.fields.filter.isNone = true then do
      let fields ← checked.fields.resolvedPartialValueSide document outer scope read hUnfiltered
      pure (.evaluated (checked.quantifier.evalClassified fields
        (.ofResolved checked.resolvedValuesSide)))
  else
    pure .skippedHaving

end CheckedStarEnumerationValueListSource

end A12Kernel
