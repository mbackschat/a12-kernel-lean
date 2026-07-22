import A12Kernel.Elaboration.StarPath

/-! # Checked nested String-star literal value lists

This capsule admits one unfiltered general starred String field against a nonempty literal token list. Topology, declaration-owned cell checking, partial relevance, and quantifier behavior remain with their shared owners.
-/

namespace A12Kernel

/-- One parser-independent starred String-fields/literal-values source. -/
structure SurfaceStarStringValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceStarFieldPath
  values : List String
  deriving Repr, DecidableEq

/-- One general starred field path certified as String-valued against its exact model declaration. -/
structure CheckedStarStringSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  field : FlatStringField
  fieldOwned : source.declaration.policy.kind = .string

/-- A checked nested String star and its nonempty literal side. -/
structure CheckedStarStringValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  fields : CheckedStarStringSource model
  firstValue : String
  restValues : List String

inductive StarStringValueListElabError where
  | path (error : StarPathElabError)
  | fieldNotString (path : List String) (actual : SurfaceScalarKind)
  | emptyValues
  deriving Repr, DecidableEq

/-- Reuse the general checked star path, then retain only an exact String declaration and a nonempty literal side. -/
def elaborateStarStringValueListSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarStringValueListSource) :
    Except StarStringValueListElabError
      (CheckedStarStringValueListSource model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored.fields
    |>.mapError .path
  match hKind : source.declaration.policy.kind with
  | .string =>
      match authored.values with
      | [] => throw .emptyValues
      | firstValue :: restValues =>
          pure {
            quantifier := authored.quantifier
            fields := {
              source
              field := { id := source.declaration.id }
              fieldOwned := hKind }
            firstValue
            restValues }
  | actual => throw (.fieldNotString source.declaration.path actual.surfaceKind)

namespace CheckedStarStringSource

/-- Classify one resolved leaf through declaration-owned String checking and the existing normalized token cell. -/
def valueListCell (checked : CheckedStarStringSource model)
    (read : Env → FieldId → RawCell) (environment : Env) : ValueListCell .token :=
  let context : FlatContext := {
    read := fun id =>
      if id == checked.field.id then checked.source.checkedCell read environment
      else malformedCheckedCell }
  (FlatTextFieldOperand.string checked.field).valueListCell context

/-- Resolve nested topology once and preserve canonical leaf order plus hierarchical omitted-tail state. -/
def resolvedValueSide (checked : CheckedStarStringSource model)
    (document : Document) (outer : Env) (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedValueListSide document outer (checked.valueListCell read)

/-- Resolve nested topology once, remove nonrelevant leaves before String checking, and retain the separate wildcard/ancestor extent fact. -/
def resolvedPartialValueSide (checked : CheckedStarStringSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListQuantifierSide .token) :=
  checked.source.resolvedPartialValueListSide document outer scope
    (checked.valueListCell read)

end CheckedStarStringSource

namespace CheckedStarStringValueListSource

def values (checked : CheckedStarStringValueListSource model) : List String :=
  checked.firstValue :: checked.restValues

def resolvedValuesSide (checked : CheckedStarStringValueListSource model) :
    ResolvedValueListSide .token :=
  literalTokenValueListSide checked.values

/-- Evaluate the checked full-validation fragment through the shared topology and quantifier owners. -/
def evaluateFull (checked : CheckedStarStringValueListSource model)
    (document : Document) (outer : Env) (read : Env → FieldId → RawCell) :
    Except StarAddressingError Verdict := do
  let fields ← checked.fields.resolvedValueSide document outer read
  pure (checked.quantifier.eval fields checked.resolvedValuesSide)

/-- Evaluate partial validation by classifying relevance per expanded cell before any String read; literal members are always relevant. -/
def evaluatePartial (checked : CheckedStarStringValueListSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Except StarAddressingError Verdict := do
  let fields ← checked.fields.resolvedPartialValueSide document outer scope read
  pure (checked.quantifier.evalClassified fields
    (.ofResolved checked.resolvedValuesSide))

end CheckedStarStringValueListSource

end A12Kernel
