import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StarNumber
import A12Kernel.Elaboration.CheckedStarDocument

/-! # Shared checked Number entity lists

This boundary owns the common authoring contract for Number-valued entity lists consumed by `FirstFilledValue`, `Sum`, `MinValue`, `MaxValue`, and Number-valued `NumberOfDifferentValues`. It resolves every direct, plain-star, and filtered-star slot in authored order, rejects only repeated direct fields, requires either multiple slots or one starred slot, and certifies every declaration as Number-valued. Runtime consumers retain their own scan semantics.
-/

namespace A12Kernel

namespace CheckedDocument

/-- Classify one model-owned Number field instance from the immutable checked input. The caller retains the authored operand and traversal; this query owns only address resolution and phase observation. -/
def numberValueListCellAt (document : CheckedDocument model)
    (phase : Phase) (environment : Env) (field : FlatNumberField) :
    Except CheckedAddressingError (ValueListCell .number) := do
  let addressed ← document.addressedCell environment field.id
  pure (observeCell phase addressed.cell).asNumberValueListCell

end CheckedDocument

/-- Number entity-list authors use the shared kind-independent syntax. -/
abbrev SurfaceNumberEntityOperand := SurfaceFieldEntityOperand

/-- Number entity-list authors use the shared nonempty source shape. -/
abbrev SurfaceNumberEntitySource := SurfaceFieldEntitySource

/-- Consumer-neutral name for the established direct nonempty Number field-list payload. -/
abbrev ResolvedDirectNumberEntityFields := ResolvedNumericAggregateFields

/-- One direct nonrepeatable Number declaration certified against the source model. -/
structure CheckedNumberEntityField (model : FlatModel) where
  declaration : FlatFieldDecl
  field : FlatNumberField
  admitted : model.admitsField (.number field) = true
  fieldOwned : declaration.toNumberField? = some field

/-- A checked Number slot retains exactly the owner needed by its direct, plain-star, or filtered-star runtime consumer. -/
inductive CheckedNumberEntityOperand (model : FlatModel) where
  | field (source : CheckedNumberEntityField model)
  | star (source : CheckedStarNumberSource model)
  | starHaving (source : CheckedStarNumberHavingSource model)

namespace CheckedNumberEntityOperand

def directFieldId? : CheckedNumberEntityOperand model → Option FieldId
  | .field source => some source.field.id
  | .star _ | .starHaving _ => none

def directField? :
    CheckedNumberEntityOperand model → Option FlatNumberField
  | .field source => some source.field
  | .star _ | .starHaving _ => none

def isStar : CheckedNumberEntityOperand model → Bool
  | .field _ => false
  | .star _ | .starHaving _ => true

def hasHaving : CheckedNumberEntityOperand model → Bool
  | .starHaving _ => true
  | .field _ | .star _ => false

def scaleSummary : CheckedNumberEntityOperand model → NumericScaleSummary
  | .field source => NumericScaleSummary.field source.field.info.scale
  | .star source => NumericScaleSummary.field source.field.info.scale
  | .starHaving source => NumericScaleSummary.field source.source.field.info.scale

def declarationSigned : CheckedNumberEntityOperand model → Bool
  | .field source => source.field.info.signed
  | .star source => source.field.info.signed
  | .starHaving source => source.source.field.info.signed

def referencesField (field : FieldId) :
    CheckedNumberEntityOperand model → Bool
  | .field source => source.field.id == field
  | .star source => source.field.id == field
  | .starHaving source =>
      source.source.field.id == field ||
        source.having.referencesField field

end CheckedNumberEntityOperand

def firstDuplicateDirectNumberEntityField? :
    List (CheckedNumberEntityOperand model) → Option FieldId
  | operands => firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

/-- A checked nonempty homogeneous Number entity list with kernel-valid cardinality and direct-reference uniqueness. Wildcarded occurrences remain independent authored slots. -/
structure CheckedNumberEntitySource (model : FlatModel) where
  first : CheckedNumberEntityOperand model
  rest : List (CheckedNumberEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isStar || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectNumberEntityField? (first :: rest) = none

namespace CheckedNumberEntitySource

def operands (checked : CheckedNumberEntitySource model) :
    List (CheckedNumberEntityOperand model) :=
  checked.first :: checked.rest

/-- Whether this checked list contains a filtered wildcard slot. Partial validation uses this only as a rule-level early-skip discriminator; it never evaluates the filter. -/
def hasHaving (checked : CheckedNumberEntitySource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

/-- Number entity-list operations derive the union/max scale of every authored declaration and gain no literal expansion capability. -/
def scaleSummary (checked : CheckedNumberEntitySource model) :
    NumericScaleSummary :=
  checked.rest.foldl
    (fun summary operand => summary.union operand.scaleSummary)
    checked.first.scaleSummary

def aggregateScaleSummary (op : NumericAggregateOp)
    (checked : CheckedNumberEntitySource model) : NumericScaleSummary :=
  match op with
  | .sum | .minimum | .maximum => checked.scaleSummary
  | .distinctCount => NumericScaleSummary.field 0

def referencesField (checked : CheckedNumberEntitySource model)
    (field : FieldId) : Bool :=
  checked.operands.any (·.referencesField field)

def directFields? (checked : CheckedNumberEntitySource model) :
    Option (FlatNumberField × List FlatNumberField) := do
  let first ← checked.first.directField?
  let rest ← checked.rest.mapM CheckedNumberEntityOperand.directField?
  pure (first, rest)

/-- Recover the legacy direct aggregate payload exactly when every checked entity-list operand is nonrepeatable. Scalar computation and generated validation share this narrowing rather than reconstructing or rechecking source syntax. -/
def directResolvedFields?
    (checked : CheckedNumberEntitySource model) :
    Option ResolvedDirectNumberEntityFields := do
  let (first, rest) ← checked.directFields?
  pure { first, rest }

/-- Compatibility name for aggregate consumers of the common direct field-list narrowing. -/
def directAggregateFields?
    (checked : CheckedNumberEntitySource model) :
    Option ResolvedNumericAggregateFields :=
  checked.directResolvedFields?

end CheckedNumberEntitySource

inductive NumberEntityElabError where
  | resolve (error : ResolveError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | star (error : StarNumberElabError)
  | tooFewFields
  | duplicateOperand (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

private def NumberEntityElabError.ofShape : FieldEntityShapeElabError →
    NumberEntityElabError
  | .resolve error => .resolve error
  | .starPath error => .star (.path error)
  | .tooFewFields => .tooFewFields
  | .duplicateOperand field => .duplicateOperand field

private def certifyStarNumber (source : CheckedStarFieldPath model) :
    Except NumberEntityElabError (CheckedStarNumberSource model) :=
  match hField : source.declaration.toNumberField? with
  | none => throw (.star (.fieldNotNumber source.declaration.path))
  | some field => pure { source, field, fieldOwned := hField }

private def certifyNumberEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except NumberEntityElabError (CheckedNumberEntityOperand model)
  | .field declaration =>
      match hField : declaration.toNumberField? with
      | none => throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)
      | some field =>
          if hAdmitted : model.admitsField (.number field) = true then
            pure (.field {
              declaration
              field
              admitted := hAdmitted
              fieldOwned := hField })
          else
            throw .incoherentCore
  | .star source => do
      pure (.star (← certifyStarNumber source))
  | .starHaving source having => do
      let numberSource ← certifyStarNumber source
      let filter ← elaborateStarHavingCore model declaringGroup numberSource.source having
        |>.mapError fun error => .star (.having error)
      pure (.starHaving { source := numberSource, declaringGroup, filter })

private def certifyNumberEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except NumberEntityElabError (List (CheckedNumberEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyNumberEntityOperand model declaringGroup operand) ::
        (← certifyNumberEntityOperands model declaringGroup remaining))

/-- Validate one Number entity list in kernel order: resolve all references, reject repeated direct fields, require multiple fields or a wildcard, then certify the common Number kind. Wildcarded occurrences are not deduplicated in an ordinary document model. -/
def elaborateNumberEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberEntitySource) :
    Except NumberEntityElabError (CheckedNumberEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError NumberEntityElabError.ofShape
  let first ← certifyNumberEntityOperand model declaringGroup shape.first
  let rest ← certifyNumberEntityOperands model declaringGroup shape.rest
  if hMultiplicity : (first.isStar || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectNumberEntityField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        first
        rest
        modelWellFormed := shape.modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

/-- One authored Number operand resolved against the immutable checked input. The source retains declaration/filter metadata; the optional topology retains every canonical candidate environment, while `addressedCells` retains exactly the relevant or filter-selected cells that were read. -/
structure ResolvedCheckedNumberEntityOperand (model : FlatModel) where
  private mk ::
  source : CheckedNumberEntityOperand model
  core : ResolvedCheckedEntityOperandCore

namespace ResolvedCheckedNumberEntityOperand

def topology (resolved : ResolvedCheckedNumberEntityOperand model) :
    Option ResolvedStarTopology :=
  resolved.core.topology

def addressedCells (resolved : ResolvedCheckedNumberEntityOperand model) :
    List CheckedAddressedCell :=
  resolved.core.addressedCells

def hasUninstantiatedTail
    (resolved : ResolvedCheckedNumberEntityOperand model) : Bool :=
  resolved.core.hasUninstantiatedTail

def hasHaving (resolved : ResolvedCheckedNumberEntityOperand model) : Bool :=
  resolved.core.hasHaving

def hasNonRelevant
    (resolved : ResolvedCheckedNumberEntityOperand model) : Bool :=
  resolved.core.hasNonRelevant

/-- Project the rich addressed operand to the existing semantic side without losing its operand-local structural metadata. -/
def valueListSideAt (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) : ResolvedValueListSide .number :=
  { cells := resolved.core.addressedCells.map fun addressed =>
      (observeCell phase addressed.cell).asNumberValueListCell
    hasUninstantiatedTail := resolved.core.hasUninstantiatedTail
    hasHaving := resolved.core.hasHaving
    hasNonRelevant := resolved.core.hasNonRelevant }

end ResolvedCheckedNumberEntityOperand

namespace CheckedNumberEntityOperand

/-- Resolve one full-validation operand through the sole checked topology, filter, and addressed-cell owners. -/
def resolveCheckedValidationOperand
    (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityOperand model) :=
  match source with
  | .field direct => do
      let core ← document.resolveCheckedDirectEntityOperandCore direct.field.id
      pure { source, core }
  | .star starSource => do
      let core ← starSource.source.resolveCheckedValidationEntityOperandCore
        document outer none
      pure { source, core }
  | .starHaving filtered => do
      let core ←
        filtered.source.source.resolveCheckedValidationEntityOperandCore
          document outer (some filtered.having)
      pure { source, core }

/-- Resolve one unfiltered partial-validation operand. Direct masking precedes its read; a star retains canonical topology, reads only relevant concrete cells, and records incomplete extent on that exact authored operand. -/
def resolveCheckedPartialValidationOperand
    (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityOperand model) :=
  match source with
  | .field direct =>
      if scope.coversCell model direct.declaration.path [] then do
        let core ← document.resolveCheckedDirectEntityOperandCore direct.field.id
        pure { source, core }
      else
        pure { source, core := .nonRelevant }
  | .star starSource => do
      let core ←
        starSource.source.resolveCheckedPartialValidationEntityOperandCore
          document outer scope
      pure { source, core }
  | .starHaving _ =>
      -- The owning rule checks `hasHaving` and skips before any operand resolver.
      pure { source, core := .skippedHaving }

end CheckedNumberEntityOperand

end A12Kernel
