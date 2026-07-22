import A12Kernel.Elaboration.Correlation

/-! # Checked nested String-star value lists

This capsule admits one general starred String field against a nonempty literal token list and the complementary one-direct-field/starred-values shape, with an optional checked `Having` on either starred operand. Topology, filter selection, declaration-owned cell checking, partial relevance, and quantifier behavior remain with their shared owners.
-/

namespace A12Kernel

/-- One parser-independent starred String-fields/literal-values source. -/
structure SurfaceStarStringValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceStarFieldPath
  values : List String
  having : Option SurfaceCorrelatedHaving := none
  deriving Repr, DecidableEq

/-- One direct nonrepeatable String field tested against a general starred String values column. -/
structure SurfaceStringValueListStarValuesSource where
  quantifier : ValueListQuantifier
  field : SurfaceFieldPath
  values : SurfaceStarFieldPath
  having : Option SurfaceCorrelatedHaving := none
  deriving Repr, DecidableEq

/-- One general starred field path certified as String-valued against its exact model declaration. -/
structure CheckedStarStringSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  field : FlatStringField
  fieldOwned : source.declaration.toStringValueField? = some field
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)

/-- A checked nested String star and its nonempty literal side. -/
structure CheckedStarStringValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  fields : CheckedStarStringSource model
  firstValue : String
  restValues : List String

/-- A checked direct String field and general starred String values side. -/
structure CheckedStringValueListStarValuesSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  fieldDeclaration : FlatFieldDecl
  field : FlatStringField
  fieldOwned : fieldDeclaration.toStringValueField? = some field
  declarationOwned : model.fields.contains fieldDeclaration = true
  admitted : model.admitsField (.string field) = true
  values : CheckedStarStringSource model

inductive StarStringValueListElabError where
  | path (error : StarPathElabError)
  | fieldNotString (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | having (error : CorrelationElabError)
  | emptyValues
  | incoherentCore
  deriving Repr, DecidableEq

/-- Reuse the general checked star path, then retain its exact String declaration. -/
def elaborateStarStringSource (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceStarFieldPath)
    (having : Option SurfaceCorrelatedHaving := none) :
    Except StarStringValueListElabError (CheckedStarStringSource model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored |>.mapError .path
  match hField : source.declaration.toStringValueField? with
  | some field =>
      let filter ← match having with
        | none => pure none
        | some authoredFilter =>
            pure (some (← elaborateStarHavingCore model declaringGroup source
              authoredFilter |>.mapError .having))
      pure {
        source
        field
        fieldOwned := hField
        declaringGroup
        filter }
  | none =>
      if source.declaration.isRawString then
        throw (.rawStringValue source.declaration.path)
      else
        throw (.fieldNotString source.declaration.path
          source.declaration.policy.kind.surfaceKind)

/-- Reuse the general checked star path, then retain only an exact String declaration and a nonempty literal side. -/
def elaborateStarStringValueListSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarStringValueListSource) :
    Except StarStringValueListElabError
      (CheckedStarStringValueListSource model) := do
  let fields ← elaborateStarStringSource model declaringGroup authored.fields authored.having
  match authored.values with
  | [] => throw .emptyValues
  | firstValue :: restValues => pure {
      quantifier := authored.quantifier
      fields
      firstValue
      restValues }

/-- Validate the model through the starred side, then resolve and certify the direct nonrepeatable String field against the same model. -/
def elaborateStringValueListStarValuesSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceStringValueListStarValuesSource) :
    Except StarStringValueListElabError
      (CheckedStringValueListStarValuesSource model) := do
  let values ← elaborateStarStringSource model declaringGroup authored.values authored.having
  let fieldDeclaration ← model.resolveNonrepeatableFieldUnchecked declaringGroup
    authored.field |>.mapError fun error => .path (.resolve error)
  match hField : fieldDeclaration.toStringValueField? with
  | some field =>
      if hOwned : model.fields.contains fieldDeclaration = true then
        if hAdmitted : model.admitsField (.string field) = true then
          pure {
            quantifier := authored.quantifier
            fieldDeclaration
            field
            fieldOwned := hField
            declarationOwned := hOwned
            admitted := hAdmitted
            values }
        else
          throw .incoherentCore
      else
        throw .incoherentCore
  | none =>
      if fieldDeclaration.isRawString then
        throw (.rawStringValue fieldDeclaration.path)
      else
        throw (.fieldNotString fieldDeclaration.path
          fieldDeclaration.policy.kind.surfaceKind)

namespace CheckedStarStringSource

/-- Classify one resolved leaf through declaration-owned String checking and the existing normalized token cell. -/
def valueListCell (checked : CheckedStarStringSource model)
    (read : Env → FieldId → RawCell) (environment : Env) : ValueListCell .token :=
  checked.source.stringValueListCell checked.field checked.fieldOwned read environment

/-- Resolve nested topology once and preserve canonical leaf order plus hierarchical omitted-tail state. -/
def resolvedValueSide (checked : CheckedStarStringSource model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide document outer
    checked.filter filterRead (checked.valueListCell read)

/-- Resolve nested topology once, remove nonrelevant leaves before String checking, and retain the separate wildcard/ancestor extent fact. -/
def resolvedPartialValueSide (checked : CheckedStarStringSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) (_unfiltered : checked.filter.isNone = true) :
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
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError Verdict := do
  let fields ← checked.fields.resolvedValueSide document outer filterRead read
  pure (checked.quantifier.eval fields checked.resolvedValuesSide)

/-- Skip a filtered rule before topology or target reads; otherwise classify relevance per expanded cell and keep literal members always relevant. -/
def evaluatePartial (checked : CheckedStarStringValueListSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialHavingValueListResult :=
  if hUnfiltered : checked.fields.filter.isNone = true then do
      let fields ← checked.fields.resolvedPartialValueSide document outer scope read hUnfiltered
      pure (.evaluated (checked.quantifier.evalClassified fields
        (.ofResolved checked.resolvedValuesSide)))
  else
    pure .skippedHaving

end CheckedStarStringValueListSource

namespace CheckedStringValueListStarValuesSource

/-- The direct fields side is checked by its model-owned declaration and contains no star metadata. -/
def resolvedFieldsSide (checked : CheckedStringValueListStarValuesSource model)
    (raw : RawFlatContext) : ResolvedValueListSide .token :=
  flatTokenValueListSide [.string checked.field] (model.checkContext raw)

/-- Partial validation classifies the direct subject before reading it and retains its ordinary per-cell masking fact. -/
def resolvedPartialFieldsSide
    (checked : CheckedStringValueListStarValuesSource model)
    (scope : ValidationRelevanceScope) (raw : RawFlatContext) :
    ResolvedValueListQuantifierSide .token :=
  selectedFlatTokenValueListSide [.string checked.field] (model.checkContext raw)
    (fun id => id == checked.field.id &&
      scope.coversCell model checked.fieldDeclaration.path [])

/-- Evaluate a direct String fields side against the canonical starred String values side. -/
def evaluateFull (checked : CheckedStringValueListStarValuesSource model)
    (document : Document) (outer : Env) (raw : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) : Except StarAddressingError Verdict := do
  let values ← checked.values.resolvedValueSide document outer filterRead read
  pure (checked.quantifier.eval (checked.resolvedFieldsSide raw) values)

/-- Partial evaluation preserves direct per-cell relevance and the starred values side's separate wildcard/ancestor extent fact before the common asymmetric dispatcher. -/
def evaluatePartial (checked : CheckedStringValueListStarValuesSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (raw : RawFlatContext) (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialHavingValueListResult :=
  if hUnfiltered : checked.values.filter.isNone = true then do
      let values ← checked.values.resolvedPartialValueSide document outer scope read hUnfiltered
      pure (.evaluated (checked.quantifier.evalClassified
        (checked.resolvedPartialFieldsSide scope raw) values))
  else
    pure .skippedHaving

end CheckedStringValueListStarValuesSource

end A12Kernel
