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

/-- The two repetition shapes an authored group-scope slot can take. Both retain the **authored** reference: the wildcard gate reads the authored path, so a group operand and its written-out expansion are two different models and lowering one into the other can emit a model the Kernel refuses. -/
inductive CheckedNumberEntityGroupSource (model : FlatModel) where
  | fixed (reference : ResolvedGroupReference)
  | starred (source : CheckedStarredGroupSource model)

namespace CheckedNumberEntityGroupSource

def groupPath : CheckedNumberEntityGroupSource model → GroupPath
  | .fixed reference => reference.path
  | .starred source => source.group.path

def isStarred : CheckedNumberEntityGroupSource model → Bool
  | .fixed _ => false
  | .starred _ => true

/-- Repeatable levels the surrounding rule environment must already bind. A fixed group is outside every repeatable scope, so it binds nothing; a starred group binds only the levels above its own star. -/
def bindingScope : CheckedNumberEntityGroupSource model → List RepeatableLevel
  | .fixed _ => []
  | .starred source => source.path.bindingScope

end CheckedNumberEntityGroupSource

/-- One authored group-scope slot certified as Number-valued.

    `expansionOwned` and `expansionAllNumber` together are the certificate: the retained list **is** the group's recursive subtree in declaration order, nonempty by its shape, and no declaration in that subtree was dropped along the way. The second obligation is what makes the first a completeness claim rather than a filter — without it a subtree of Strings would certify as an empty selection. A consumer may therefore read the expansion off this slot without re-walking the model, while the authored reference stays available for re-rendering.

    `uniformSigned` is a **representation** obligation rather than a Kernel gate. Directional missingness reads each empty cell's own declaration, but the aggregate scan applies one signedness per authored operand, so a slot spanning declarations that disagree has no correct operand-level answer. Refusing that shape keeps the accessor sound; it claims nothing about what the Kernel admits, and widening it belongs with the runtime capsule that makes signedness per-cell. -/
structure CheckedNumberEntityGroup (model : FlatModel) where
  source : CheckedNumberEntityGroupSource model
  first : FlatNumberField
  rest : List FlatNumberField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      FlatFieldDecl.toNumberField? = first :: rest
  expansionAllNumber :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toNumberField?.isSome) = true
  uniformSigned : rest.all (·.info.signed == first.info.signed) = true

namespace CheckedNumberEntityGroup

def groupPath (group : CheckedNumberEntityGroup model) : GroupPath :=
  group.source.groupPath

def isStarred (group : CheckedNumberEntityGroup model) : Bool :=
  group.source.isStarred

/-- The certified expansion, in model declaration order. -/
def fields (group : CheckedNumberEntityGroup model) : List FlatNumberField :=
  group.first :: group.rest

/-- The union scale of the whole expansion, so a nested subgroup's wider scale reaches the list's derived scale exactly as a directly authored operand would. -/
def scaleSummary (group : CheckedNumberEntityGroup model) : NumericScaleSummary :=
  group.rest.foldl
    (fun summary field => summary.union (NumericScaleSummary.field field.info.scale))
    (NumericScaleSummary.field group.first.info.scale)

/-- Sound because `uniformSigned` forces every expanded declaration to agree. -/
def declarationSigned (group : CheckedNumberEntityGroup model) : Bool :=
  group.first.info.signed

def referencesField (group : CheckedNumberEntityGroup model)
    (field : FieldId) : Bool :=
  group.fields.any (·.id == field)

end CheckedNumberEntityGroup

/-- A checked Number slot retains exactly the owner needed by its direct, plain-star, filtered-star, or group-scope runtime consumer. -/
inductive CheckedNumberEntityOperand (model : FlatModel) where
  | field (source : CheckedNumberEntityField model)
  | star (source : CheckedStarNumberSource model)
  | starHaving (source : CheckedStarNumberHavingSource model)
  | group (source : CheckedNumberEntityGroup model)

namespace CheckedNumberEntityOperand

def directFieldId? : CheckedNumberEntityOperand model → Option FieldId
  | .field source => some source.field.id
  | .star _ | .starHaving _ | .group _ => none

def directField? :
    CheckedNumberEntityOperand model → Option FlatNumberField
  | .field source => some source.field
  | .star _ | .starHaving _ | .group _ => none

/-- The retained group slot, for a consumer that must re-render or analyse the authored operand. -/
def groupSlot? :
    CheckedNumberEntityOperand model → Option (CheckedNumberEntityGroup model)
  | .group source => some source
  | .field _ | .star _ | .starHaving _ => none

/-- Whether one authored slot satisfies the multiple-operand requirement by itself. A star denotes a row set and a group denotes a field scope, so both are already-many; this is deliberately weaker than "is a star". -/
def isAlreadyMany : CheckedNumberEntityOperand model → Bool
  | .field _ => false
  | .star _ | .starHaving _ | .group _ => true

def hasHaving : CheckedNumberEntityOperand model → Bool
  | .starHaving _ => true
  | .field _ | .star _ | .group _ => false

def scaleSummary : CheckedNumberEntityOperand model → NumericScaleSummary
  | .field source => NumericScaleSummary.field source.field.info.scale
  | .star source => NumericScaleSummary.field source.field.info.scale
  | .starHaving source => NumericScaleSummary.field source.source.field.info.scale
  | .group source => source.scaleSummary

def declarationSigned : CheckedNumberEntityOperand model → Bool
  | .field source => source.field.info.signed
  | .star source => source.field.info.signed
  | .starHaving source => source.source.field.info.signed
  | .group source => source.declarationSigned

def referencesField (field : FieldId) :
    CheckedNumberEntityOperand model → Bool
  | .field source => source.field.id == field
  | .star source => source.field.id == field
  | .starHaving source =>
      source.source.field.id == field ||
        source.having.referencesField field
  | .group source => source.referencesField field

end CheckedNumberEntityOperand

def firstDuplicateDirectNumberEntityField? :
    List (CheckedNumberEntityOperand model) → Option FieldId
  | operands => firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

/-- A checked nonempty homogeneous Number entity list with kernel-valid cardinality and direct-reference uniqueness. Wildcarded occurrences remain independent authored slots. -/
structure CheckedNumberEntitySource (model : FlatModel) where
  first : CheckedNumberEntityOperand model
  rest : List (CheckedNumberEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true
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
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | star (error : StarNumberElabError)
  /-- A group slot whose expansion contains a declaration that is not Number-valued. The Kernel's class here is each operator's own — `MVK_NO_NUMBER` under `Sum`, `MVK_NOT_SORTABLE` under the extrema — so this shared boundary names none. -/
  | groupExpansionNotNumber (path : List String)
  /-- A group slot whose subtree declares no field at all. Unmeasured, so refused without a class. -/
  | groupExpansionEmpty (path : List String)
  /-- A group slot whose expanded declarations disagree on signedness. A representation limit rather than a Kernel gate; see `CheckedNumberEntityGroup.uniformSigned`. -/
  | groupExpansionMixedSign (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

namespace NumberEntityElabError

/-- The expansion-kind gate is **each operator's own question about the expansion's values**, which is why this projection is keyed by the operator where every gate the shared checker owns is not. One group whose subtree contains a String draws three different classes here, and reading one carrier's class off a sibling is precisely the inference the Kernel refutes.

    Shape refusals delegate to the shared checker, because the star, arity, and duplicate gates do not vary by carrier.

    The **explicit** field list carries the class only under the extrema, where the equivalent written-out list is measured to draw the same unsortable code. No row places `Sum`'s or the distinct count's class on the explicit form, so it stays unprojected there rather than inheriting the group's. -/
def aggregateDiagnostic? (op : NumericAggregateOp) :
    NumberEntityElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .groupExpansionNotNumber _ =>
      match op with
      | .sum => some .noNumber
      | .minimum | .maximum => some .notSortable
      | .distinctCount => some .stringEnumAndNonStringEnum
  | .fieldKindMismatch _ _ =>
      match op with
      | .minimum | .maximum => some .notSortable
      | .sum | .distinctCount => none
  | .star _ | .groupExpansionEmpty _ | .groupExpansionMixedSign _
  | .incoherentCore => none

end NumberEntityElabError

private def certifyStarNumber (source : CheckedStarFieldPath model) :
    Except NumberEntityElabError (CheckedStarNumberSource model) :=
  match hField : source.declaration.toNumberField? with
  | none => throw (.star (.fieldNotNumber source.declaration.path))
  | some field => pure { source, field, fieldOwned := hField }

/-- Certify one authored group slot by expanding it once through the shared subtree query. The three refusals are distinct and all deliberately unprojected: `MVK_NO_NUMBER` and its siblings are each operator's own class, and this boundary has no operator. -/
private def certifyNumberEntityGroup (model : FlatModel)
    (source : CheckedNumberEntityGroupSource model) :
    Except NumberEntityElabError (CheckedNumberEntityOperand model) :=
  if hAll : (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toNumberField?.isSome) = true then
    match hExpansion :
        (model.groupSubtreeFields source.groupPath).filterMap
          FlatFieldDecl.toNumberField? with
    | [] => throw (.groupExpansionEmpty source.groupPath)
    | first :: rest =>
        if hSigned : rest.all (·.info.signed == first.info.signed) = true then
          pure (.group {
            source
            first
            rest
            expansionOwned := hExpansion
            expansionAllNumber := hAll
            uniformSigned := hSigned })
        else
          throw (.groupExpansionMixedSign source.groupPath)
  else
    throw (.groupExpansionNotNumber source.groupPath)

private def certifyNumberEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except NumberEntityElabError (CheckedNumberEntityOperand model)
  | .field declaration _ =>
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
  | .group reference => certifyNumberEntityGroup model (.fixed reference)
  | .starredGroup source => certifyNumberEntityGroup model (.starred source)

private def certifyNumberEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except NumberEntityElabError (List (CheckedNumberEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyNumberEntityOperand model declaringGroup operand) ::
        (← certifyNumberEntityOperands model declaringGroup remaining))

/-- Certify an already checked entity-list shape as Number-valued without resolving its authored
    references a second time. Consumer-specific whole-list gates run between shape and kind
    certification through this boundary. -/
def certifyNumberEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (shape : CheckedFieldEntityShape model) :
    Except NumberEntityElabError (CheckedNumberEntitySource model) := do
  let first ← certifyNumberEntityOperand model declaringGroup shape.first
  let rest ← certifyNumberEntityOperands model declaringGroup shape.rest
  if hMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true then
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

/-- Validate one Number entity list in kernel order: resolve all references, reject repeated direct fields, require multiple fields or a wildcard, then certify the common Number kind. Wildcarded occurrences are not deduplicated in an ordinary document model. -/
def elaborateNumberEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberEntitySource) :
    Except NumberEntityElabError (CheckedNumberEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError NumberEntityElabError.shape
  certifyNumberEntityShape model declaringGroup shape

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
  | .group slot => do
      let core ← document.resolveCheckedGroupEntityOperandCore
        (model.groupSubtreeFields slot.groupPath)
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
  | .group slot =>
      .error (.addressing (.unsupportedGroupOperand slot.groupPath))

end CheckedNumberEntityOperand

end A12Kernel
