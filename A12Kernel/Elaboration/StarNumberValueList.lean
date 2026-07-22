import A12Kernel.Elaboration.StarNumber

/-! # Checked nested Number-star value lists

This capsule lowers one nested starred Number field, optionally filtered by the existing
checked `Having` fragment, against a nonempty list of direct nonrepeatable Number value
fields. Runtime evaluation delegates topology, filtering, validation-phase cell
classification, and quantifier semantics to their existing owners.
-/

namespace A12Kernel

/-- The fields side of the supported checked Number value-list fragment. -/
inductive SurfaceStarNumberValueListFields where
  | star (path : SurfaceStarFieldPath)
  | starHaving (path : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

/-- One parser-independent Number value-list source. The values side is field-valued,
as required by the kernel's starred Number grammar. -/
structure SurfaceStarNumberValueListSource where
  quantifier : ValueListQuantifier
  fields : SurfaceStarNumberValueListFields
  firstValue : SurfaceFieldPath
  restValues : List SurfaceFieldPath
  deriving Repr, DecidableEq

/-- One direct Number value field certified against the exact source model. -/
structure CheckedStarNumberValueField (model : FlatModel) where
  declaration : FlatFieldDecl
  field : FlatNumberField
  admitted : model.admitsField (.number field) = true
  fieldOwned : declaration.toNumberField? = some field

/-- The fields side retains only the checked owner required by its authored form. -/
inductive CheckedStarNumberValueListFields (model : FlatModel) where
  | star (source : CheckedStarNumberSource model)
  | starHaving (source : CheckedStarNumberHavingSource model)

/-- A checked nested-star fields side and nonempty, distinct direct Number values side. -/
structure CheckedStarNumberValueListSource (model : FlatModel) where
  quantifier : ValueListQuantifier
  fields : CheckedStarNumberValueListFields model
  firstValue : CheckedStarNumberValueField model
  restValues : List (CheckedStarNumberValueField model)
  modelWellFormed : model.validate.isOk = true
  uniqueValueFields :
    FieldId.firstDuplicate?
      ((firstValue :: restValues).map (·.field.id)) = none

inductive StarNumberValueListElabError where
  | resolve (error : ResolveError)
  | fields (error : StarNumberElabError)
  | duplicateValueField (field : FieldId)
  | valueFieldNotNumber (path : List String) (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

private def elaborateStarNumberValueListFields (model : FlatModel)
    (declaringGroup : GroupPath) : SurfaceStarNumberValueListFields →
      Except StarNumberValueListElabError
        (CheckedStarNumberValueListFields model)
  | .star path => do
      pure (.star (← elaborateStarNumberSource model declaringGroup path
        |>.mapError .fields))
  | .starHaving path having => do
      pure (.starHaving (← elaborateStarNumberHavingSource model declaringGroup
        path having |>.mapError .fields))

private def resolveStarNumberValueDeclarations (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceFieldPath →
      Except StarNumberValueListElabError (List FlatFieldDecl)
  | [] => pure []
  | path :: remaining => do
      let declaration ← model.resolveNonrepeatableFieldUnchecked declaringGroup path
        |>.mapError .resolve
      pure (declaration ::
        (← resolveStarNumberValueDeclarations model declaringGroup remaining))

private def certifyStarNumberValueField (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except StarNumberValueListElabError (CheckedStarNumberValueField model) :=
  match hField : declaration.toNumberField? with
  | none => throw (.valueFieldNotNumber declaration.path
      declaration.policy.kind.surfaceKind)
  | some field =>
      if hAdmitted : model.admitsField (.number field) = true then
        pure { declaration, field, admitted := hAdmitted, fieldOwned := hField }
      else
        throw .incoherentCore

private def certifyStarNumberValueFields (model : FlatModel) :
    List FlatFieldDecl →
      Except StarNumberValueListElabError
        (List (CheckedStarNumberValueField model))
  | [] => pure []
  | declaration :: remaining => do
      pure ((← certifyStarNumberValueField model declaration) ::
        (← certifyStarNumberValueFields model remaining))

/-- Validate the model once, resolve both sides, reject repeated direct value fields
before kind certification, and retain the existing checked star and Number-field owners. -/
def elaborateStarNumberValueListSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarNumberValueListSource) :
    Except StarNumberValueListElabError
      (CheckedStarNumberValueListSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let fields ← elaborateStarNumberValueListFields model declaringGroup authored.fields
      let firstDeclaration ← model.resolveNonrepeatableFieldUnchecked declaringGroup
        authored.firstValue |>.mapError .resolve
      let restDeclarations ← resolveStarNumberValueDeclarations model declaringGroup
        authored.restValues
      match FieldId.firstDuplicate?
          ((firstDeclaration :: restDeclarations).map (·.id)) with
      | some field => throw (.duplicateValueField field)
      | none => do
          let firstValue ← certifyStarNumberValueField model firstDeclaration
          let restValues ← certifyStarNumberValueFields model restDeclarations
          match hUnique : FieldId.firstDuplicate?
              ((firstValue :: restValues).map (·.field.id)) with
          | some _ => throw .incoherentCore
          | none => pure {
              quantifier := authored.quantifier
              fields
              firstValue
              restValues
              modelWellFormed := by rw [hModel]; rfl
              uniqueValueFields := hUnique }

namespace CheckedStarNumberValueListFields

/-- Resolve nested topology and apply any checked filter before target classification. -/
def resolvedValueSide (checked : CheckedStarNumberValueListFields model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .star source => source.resolvedValueSide document outer read
  | .starHaving source => source.resolvedValueSide document outer filterRead read

end CheckedStarNumberValueListFields

namespace CheckedStarNumberValueListSource

def values (checked : CheckedStarNumberValueListSource model) :
    List (CheckedStarNumberValueField model) :=
  checked.firstValue :: checked.restValues

/-- Direct value fields are classified with their model-owned validation policies, in
authored order, with neither a filter nor an uninstantiated tail. -/
def resolvedValuesSide (checked : CheckedStarNumberValueListSource model)
    (raw : RawFlatContext) : ResolvedValueListSide .number :=
  let context := model.checkContext raw
  { cells := checked.values.map fun value => value.field.valueListCell context
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Evaluate the supported full-validation fragment through the existing checked star
and resolved value-list quantifier boundaries. Whole-rule content, metadata, and message
emission remain with the later general checked validation owner. -/
def evaluateFull (checked : CheckedStarNumberValueListSource model)
    (document : Document) (outer : Env) (raw : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError Verdict := do
  let fields ← checked.fields.resolvedValueSide document outer filterRead starRead
  pure (checked.quantifier.eval fields (checked.resolvedValuesSide raw))

end CheckedStarNumberValueListSource

end A12Kernel
