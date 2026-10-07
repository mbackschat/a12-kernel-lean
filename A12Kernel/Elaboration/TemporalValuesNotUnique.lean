import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.KeyedEntityExtent
import A12Kernel.Semantics.NumericAggregate

/-! # Checked temporal `FieldValuesNotUnique`

The fourth comparability category of one operator. Slot admission, authored order, repeated-direct rejection, and the multiple-slots-or-one-star rule stay in `FieldEntityList`; the ordered fused scan and the whole polarity account stay in `NumericAggregate`. This module owns only what is temporal about the temporal overload: the admission gate and the compared identity.

**Admission** is one identical declared **format string** across every operand, keyed on the format rather than the kind. Real-kernel authoring accepts a DATE declared `yyyy` beside a DATE_FRAGMENT declared `yyyy` across two kinds while refusing two DATE fields differing only in declared format, so a kind-equality reading gets both directions wrong. Because a DATE_FRAGMENT is a `.date` declaration with a partial mode here, that cross-kind list is two `.temporal .date` operands whose partial modes differ and whose format agrees, and this gate admits it. Note that the kernel's two kinds therefore collapse to one at this boundary, so a local case can separate format equality from kind equality only in the refusing direction; the admitting direction separates it from whole-policy equality instead.

**The compared identity is the operand's exact stored text**, not its decoded value. That is what the *dynamic* kernel runtime reads for this operator, with the generated-Java strategy unread for this comparison, and it is deliberately a different reading from the decoded date `NumberOfDifferentValues` would use over the same entity lists. **That contrast is now measured on both sides**, where an earlier version of this note had the neighbour's half as merely expected because no temporal `NumberOfDifferentValues` overload existed yet. One does — [`TemporalDistinctCount.lean`](TemporalDistinctCount.lean) — and its compared identity is the decoded value at the list's shared declared component set, Kernel-measured with the reversed document as separator ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-distinct-count-component-omitting-fold), accepted at `SPEC-2026-09-06-08`). So two operators over the same entity lists genuinely compare different things: one the stored text, the other the decoded value. A reimplementer sharing one identity between them is wrong in a way no single-operator test can see. The neighbour's own conformance pins it on the one list that separates the two identities — a group carrying a single component set in two spellings, which this operator refuses and that one admits: `2024-03-05` beside `05.03.2024` counts **one** value there, where a stored-text identity would count two. Under the mandatory single format the stored-text and decoded accounts agree *if* one declared format admits one text per value; that assumption is unmeasured and [`SG7`](../../docs/SEMANTICS-GAPS.md) owns its witness class. Reusing the canonical token atom is therefore exact rather than a rendering: the value compared is the stored text itself, so no normal form is invented.

One admission fact is an annotation rather than a gate. A declaration whose declared format disagrees with its own kind family is not refused by this gate, because format equality is stated as a total function and the authorability of such a declaration is unmeasured. DATE_RANGE is represented by its distinct flat declaration kind and is refused before this temporal format scan by the shared measured kind gate.
-/

namespace A12Kernel

inductive TemporalValuesNotUniqueElabError where
  | shape (error : FieldEntityShapeElabError)
  /-- An operand whose kind the operator refuses outright, which the Kernel's **first** gate reports. -/
  | inadmissibleKind (path : List String) (actual : SurfaceScalarKind)
  /-- An operand of an individually admissible kind drawn from another comparability category, which the Kernel's **second** gate reports. -/
  | mixedCategories (path : List String) (actual : SurfaceScalarKind)
  /-- A temporal operand whose declaration carries no coherent declared format. The operator's gate and its compared identity both need the exact format, so an incomplete declaration fails closed rather than defaulting here.

      This is a **flat-model** state, not a Kernel one, and the difference is now measured: a temporal field may declare no format and the Kernel resolves its kind's default, producing a format string that compares equal to the default spelling at this very gate ([checkpoint](../../docs/SOURCES.md#src-temporal-declaration-without-a-format)). A flat model built by a loader that performs that resolution never reaches this arm; one built without it does, and fails closed. Claims no Kernel class because the Kernel draws none — it admits the declaration. -/
  | missingDeclaredFormat (path : List String)
  | mixedDeclaredFormats (path : List String) (found expected : String)
  | having (error : CorrelationElabError)
  /-- A group slot whose recursive subtree declares no field, reached only as `RuleGroup` in a rule declared at an empty repeatable group; the shared shape refuses an explicit empty starred group first, as `MVK_GROUP_IS_EMPTY`. That spelling is unmeasured, so no class is claimed. -/
  | groupExpansionEmpty (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One temporal declaration admitted by this operator, carrying the exact declared format its admission gate reads. -/
structure CheckedTemporalUniquenessField where
  private mk ::
  declaration : FlatFieldDecl
  policy : TemporalTargetPolicy
  policyOwned : declaration.toTemporalTargetPolicy? = some policy
  deriving Repr

namespace CheckedTemporalUniquenessField

def format (checked : CheckedTemporalUniquenessField) : String :=
  checked.policy.format

def path (checked : CheckedTemporalUniquenessField) : List String :=
  checked.declaration.path

/-- The declared **precision** this operand carries. Exposed here rather than gated here: this
    operator admits every precision, and its neighbour the distinct count refuses all three
    ([checkpoint](../../docs/SOURCES.md#src-partial-date-precision-operand-gate)), so the accessor
    belongs to the shared certificate and the gate to the carrier that has one. -/
def partialMode (checked : CheckedTemporalUniquenessField) : TemporalPartialMode :=
  checked.policy.partialMode

end CheckedTemporalUniquenessField

/-- Certify one resolved declaration as a temporal operand. A non-temporal kind and a temporal kind without a coherent declared format are distinct refusals: the first is the wrong comparability category, the second an insufficient declaration. -/
def certifyTemporalUniquenessField (declaration : FlatFieldDecl) :
    Except TemporalValuesNotUniqueElabError CheckedTemporalUniquenessField :=
  match hPolicy : declaration.toTemporalTargetPolicy? with
  | some policy => .ok { declaration, policy, policyOwned := hPolicy }
  | none =>
      let kind := declaration.policy.kind.surfaceKind
      match kind.fieldListAdmission with
      | .category .temporal => .error (.missingDeclaredFormat declaration.path)
      | .category _ => .error (.mixedCategories declaration.path kind)
      | .refusedByKind => .error (.inadmissibleKind declaration.path kind)

/-- The option-valued form used to certify a complete group expansion without dropping a
    declaration. The detailed certifier above still owns which refusal a missing value reports. -/
def FlatFieldDecl.toTemporalUniquenessField?
    (declaration : FlatFieldDecl) : Option CheckedTemporalUniquenessField :=
  match hPolicy : declaration.toTemporalTargetPolicy? with
  | some policy => some { declaration, policy, policyOwned := hPolicy }
  | none => none

/-- Find the first temporal field whose declared format differs from `expected`. -/
def firstMismatchedTemporalFieldFormat? (expected : String) :
    List CheckedTemporalUniquenessField → Option (List String × String)
  | [] => none
  | field :: remaining =>
      if field.format == expected then
        firstMismatchedTemporalFieldFormat? expected remaining
      else
        some (field.path, field.format)

/-- A complete temporal declaration expansion behind one index selection. Format and component
agreement belong to the consuming operator, whose gates differ (spec/07 entity lists). -/
structure CheckedSelectedTemporalEntity (model : FlatModel) where
  private mk ::
  source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)
  first : CheckedTemporalUniquenessField
  rest : List CheckedTemporalUniquenessField
  expansionOwned : (match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations).filterMap FlatFieldDecl.toTemporalUniquenessField? = first :: rest
  allTemporal : (match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations).all (fun d => d.toTemporalUniquenessField?.isSome) = true

namespace CheckedSelectedTemporalEntity

def path (source : CheckedSelectedTemporalEntity model) : List String :=
  match source.source with | .inl source => source.targetDeclaration.path | .inr source => source.entityPath

def referencesField (source : CheckedSelectedTemporalEntity model) (field : FieldId) : Bool :=
  match source.source with | .inl source => source.referencesField field | .inr source => source.referencesField field

/-- Selection supplies addresses and omission; each operator projects the retained declaration's
cell using its own identity, including stored text for uniqueness and decoded dates for counts. -/
def sideWith {kind : ValueListKind} (source : CheckedSelectedTemporalEntity model)
    (phase : Phase) (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (storedAt : Env → FieldId → Option String) (column : SemanticIndexColumnReader)
    (project : CheckedTemporalUniquenessField → CheckedCell → Option String → Except CheckedAddressingError (ValueListCell kind)) :
    Except CheckedAddressingError (ResolvedValueListSide kind) := do
  let index := match source.source with | .inl source => source | .inr source => source.selection.indexSource
  match ← index.selectEnvironmentWith phase column outer direct stored with
  | .unknown cause | .poison cause => pure { cells := [.unknown cause], hasUninstantiatedTail := false, hasHaving := false }
  | .empty =>
      pure {
        cells := match source.source with | .inl _ => [.empty] | .inr _ => []
        hasUninstantiatedTail := match source.source with
          | .inl _ => false
          | .inr source => match source.target with | .group _ => true | _ => false
        hasHaving := false }
  | .value environment =>
      let rows ← match source.source with
        | .inl source => pure [(source.targetDeclaration, [environment], false)]
        | .inr source => source.rows document environment |>.mapError .addressing
      let cells ← rows.flatMapM fun (declaration, environments, _) => do
        let some field := (source.first :: source.rest).find? (·.declaration.id == declaration.id)
          | throw (.checkedDocumentRequired declaration.path)
        environments.mapM fun row => project field (read row declaration.id) (storedAt row declaration.id)
      pure { cells, hasUninstantiatedTail := rows.any (·.2.2), hasHaving := false }

end CheckedSelectedTemporalEntity

/-- Certify all selected declarations without importing either consumer's equality gate. -/
def certifySelectedTemporalEntity
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Except TemporalValuesNotUniqueElabError (CheckedSelectedTemporalEntity model) := do
  let declarations := match source with | .inl source => [source.targetDeclaration] | .inr source => source.declarations
  if hAll : declarations.all (fun d => d.toTemporalUniquenessField?.isSome) = true then
    match hExpansion : declarations.filterMap FlatFieldDecl.toTemporalUniquenessField? with
    | [] => throw .incoherentCore
    | first :: rest => pure { source, first, rest, expansionOwned := hExpansion, allTemporal := hAll }
  else
    match declarations.find? (fun d => d.toTemporalUniquenessField?.isNone) with
    | none => throw .incoherentCore
    | some declaration =>
        match certifyTemporalUniquenessField declaration with
        | .error error => throw error
        | .ok _ => throw .incoherentCore

/-- One authored group slot certified as a nonempty, recursively complete temporal expansion with
    one declared format. The authored group reference stays intact; `first` and `rest` are its
    declaration-level certificate, not replacement authored operands. -/
structure CheckedTemporalUniquenessGroup (model : FlatModel) where
  source : CheckedEntityGroupSource model
  first : CheckedTemporalUniquenessField
  rest : List CheckedTemporalUniquenessField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      FlatFieldDecl.toTemporalUniquenessField? = first :: rest
  expansionAllTemporal :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toTemporalUniquenessField?.isSome) = true
  oneDeclaredFormat :
    firstMismatchedTemporalFieldFormat? first.format rest = none

namespace CheckedTemporalUniquenessGroup

def groupPath (group : CheckedTemporalUniquenessGroup model) : GroupPath :=
  group.source.groupPath

def isStarred (group : CheckedTemporalUniquenessGroup model) : Bool :=
  group.source.isStarred

def fields (group : CheckedTemporalUniquenessGroup model) :
    List CheckedTemporalUniquenessField :=
  group.first :: group.rest

def declarations (group : CheckedTemporalUniquenessGroup model) :
    List FlatFieldDecl :=
  group.fields.map (·.declaration)

def format (group : CheckedTemporalUniquenessGroup model) : String :=
  group.first.format

/-- The leading declaration's precision; exact format agreement does not make partial modes uniform. -/
def partialMode (group : CheckedTemporalUniquenessGroup model) : TemporalPartialMode :=
  group.first.partialMode

end CheckedTemporalUniquenessGroup

/-- One certified temporal slot. A filter belongs to its exact authored wildcard occurrence. -/
inductive CheckedTemporalUniquenessOperand (model : FlatModel) where
  | field (source : CheckedTemporalUniquenessField)
  | star (path : CheckedStarFieldPath model)
      (source : CheckedTemporalUniquenessField)
      (filter : Option CorrelatedHaving)
  | group (source : CheckedTemporalUniquenessGroup model)
  | selected (source : CheckedSelectedTemporalEntity model)
      (oneDeclaredFormat : firstMismatchedTemporalFieldFormat? source.first.format source.rest = none)

namespace CheckedTemporalUniquenessOperand

def format (operand : CheckedTemporalUniquenessOperand model) : String :=
  match operand with
  | .field source | .star _ source _ => source.format
  | .group source => source.format
  | .selected source _ => source.first.format

def partialMode (operand : CheckedTemporalUniquenessOperand model) :
    TemporalPartialMode :=
  match operand with
  | .field source | .star _ source _ => source.partialMode
  | .group source => source.partialMode
  | .selected source _ => source.first.partialMode

def path (operand : CheckedTemporalUniquenessOperand model) : List String :=
  match operand with
  | .field source | .star _ source _ => source.path
  | .group source => source.groupPath
  | .selected source _ => source.path

def groupSlot? : CheckedTemporalUniquenessOperand model →
    Option (CheckedTemporalUniquenessGroup model)
  | .group source => some source
  | .field _ | .star _ _ _ | .selected _ _ => none

def hasHaving : CheckedTemporalUniquenessOperand model → Bool
  | .field _ | .star _ _ none => false
  | .star _ _ (some _) => true
  | .group _ | .selected _ _ => false

/-- Resolve one slot against the immutable checked document through the shared kind-neutral entity core, which owns topology, addressing, filter selection, and omitted-tail extent. -/
def resolveValidationCore (operand : CheckedTemporalUniquenessOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore :=
  match operand with
  | .selected source _ => throw (.checkedDocumentRequired source.path)
  | .field source =>
      document.resolveCheckedDirectEntityOperandCore source.declaration.id
  | .star path _ filter =>
      path.resolveCheckedValidationEntityOperandCore (world := world) document outer filter
  | .group source =>
      document.resolveCheckedGroupEntityOperandCore outer
        source.source.boundLevelCount source.declarations

end CheckedTemporalUniquenessOperand

/-- Find the first operand whose declared format differs from the list's, reporting its path and both formats. Public because the certificate below states its gate in terms of this scan, so an external law has to speak about it. -/
def firstMismatchedTemporalFormat? (expected : String) :
    List (CheckedTemporalUniquenessOperand model) →
      Option (List String × String)
  | [] => none
  | operand :: remaining =>
      if operand.format == expected then
        firstMismatchedTemporalFormat? expected remaining
      else
        some (operand.path, operand.format)

/-- One checked temporal `FieldValuesNotUnique` operand list, certified to carry a single declared format. -/
structure CheckedTemporalValuesNotUniqueSource (model : FlatModel) where
  private mk ::
  /-- The shared shape this list was certified from. It carries model validity, the multiple-slots-or-one-star rule, and repeated-direct rejection; `first`/`rest` are its own slots certified in the same order. -/
  shape : CheckedFieldEntityShape model
  first : CheckedTemporalUniquenessOperand model
  rest : List (CheckedTemporalUniquenessOperand model)
  oneDeclaredFormat :
    firstMismatchedTemporalFormat? first.format rest = none

namespace CheckedTemporalValuesNotUniqueSource

def operands (checked : CheckedTemporalValuesNotUniqueSource model) :
    List (CheckedTemporalUniquenessOperand model) :=
  checked.first :: checked.rest

/-- The list's single declared format, which every operand shares by construction. -/
def format (checked : CheckedTemporalValuesNotUniqueSource model) : String :=
  checked.first.format

end CheckedTemporalValuesNotUniqueSource

private def certifyTemporalUniquenessGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except TemporalValuesNotUniqueElabError
      (CheckedTemporalUniquenessOperand model) :=
  let declarations := model.groupSubtreeFields source.groupPath
  if hAll : declarations.all
      (fun declaration => declaration.toTemporalUniquenessField?.isSome) = true then
    match hExpansion : declarations.filterMap
        FlatFieldDecl.toTemporalUniquenessField? with
    | [] => throw (.groupExpansionEmpty source.groupPath)
    | first :: rest =>
        match hFormats :
            firstMismatchedTemporalFieldFormat? first.format rest with
        | some (path, found) =>
            throw (.mixedDeclaredFormats path found first.format)
        | none =>
            pure (.group {
              source
              first
              rest
              expansionOwned := hExpansion
              expansionAllTemporal := hAll
              oneDeclaredFormat := hFormats })
  else
    match declarations.find? fun declaration =>
        declaration.toTemporalUniquenessField?.isNone with
    | some declaration =>
        match certifyTemporalUniquenessField declaration with
        | .error error => throw error
        | .ok _ => throw .incoherentCore
    | none => throw .incoherentCore

private def certifySelectedUniqueness
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Except TemporalValuesNotUniqueElabError (CheckedTemporalUniquenessOperand model) := do
  let source ← certifySelectedTemporalEntity source
  match hFormat : firstMismatchedTemporalFieldFormat? source.first.format source.rest with
  | some (path, found) => throw (.mixedDeclaredFormats path found source.first.format)
  | none => pure (.selected source hFormat)

/-- Certify uniqueness operands with exact format agreement. Distinct count reuses the scalar
certificates, but certifies group and selected expansions against its own component-set gate. -/
def certifyTemporalUniquenessOperand (model : FlatModel)
    (declaringGroup : GroupPath) (operand : ResolvedFieldEntityOperand model)
    (bindingGroup : GroupPath := declaringGroup) :
      Except TemporalValuesNotUniqueElabError
        (CheckedTemporalUniquenessOperand model) :=
  match operand with
  | .indexed source => certifySelectedUniqueness (.inl source)
  | .keyed source => certifySelectedUniqueness (.inr source)
  | .field declaration _ =>
      do pure (.field (← certifyTemporalUniquenessField declaration))
  | .star source =>
      do pure (.star source (← certifyTemporalUniquenessField source.declaration)
        none)
  | .starHaving source having => do
      let field ← certifyTemporalUniquenessField source.declaration
      let filter ← elaborateStarHavingCore model declaringGroup source having bindingGroup
        |>.mapError .having
      pure (.star source field (some filter.condition))
  | .group reference =>
      certifyTemporalUniquenessGroup model (.fixed reference)
  | .starredGroup source =>
      certifyTemporalUniquenessGroup model (.starred source)
  | .starredGroupPresence source =>
      certifyTemporalUniquenessGroup model (.starredPresence source)

def certifyTemporalUniquenessOperands (model : FlatModel)
    (declaringGroup : GroupPath) (operands : List (ResolvedFieldEntityOperand model))
    (bindingGroup : GroupPath := declaringGroup) :
    Except TemporalValuesNotUniqueElabError (List (CheckedTemporalUniquenessOperand model)) :=
  operands.mapM (fun operand =>
    certifyTemporalUniquenessOperand model declaringGroup operand bindingGroup)

/-- Report the first operand the Kernel's **kind** gate refuses, scanning the whole list. This runs before any category or format decision because the gate order is observable: a Boolean or Confirm beside a String reports the kind code with the mixing code absent. Public because the gate-order law has to speak about this scan. -/
def firstKindGateRefusal? :
    List (ResolvedFieldEntityOperand model) →
      Option TemporalValuesNotUniqueElabError
  | operands =>
      match firstFieldListKindRefusal? operands with
      | some refusal => some (.inadmissibleKind refusal.path refusal.actual)
      | none => none

/-- Admit one temporal operand list in the Kernel's gate order: the shared entity shape, then the kind gate over every operand, then the single-declared-format rule that shares the kind gate's code, and only then the category-mixing gate that certification reports. -/
def elaborateTemporalValuesNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource)
    (writtenGroup : GroupPath := declaringGroup) (targetGroup? : Option GroupPath := none) :
    Except TemporalValuesNotUniqueElabError
      (CheckedTemporalValuesNotUniqueSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored (fixedTargetGroup? := targetGroup?) (writtenGroup := writtenGroup)
      (categoryGate := .behindRootGate)
    |>.mapError .shape
  match firstKindGateRefusal? shape.operands with
  | some refusal => throw refusal
  | none => pure ()
  let bindingGroup := targetGroup?.getD writtenGroup
  let first ← certifyTemporalUniquenessOperand model declaringGroup shape.first bindingGroup
  let rest ← certifyTemporalUniquenessOperands model declaringGroup shape.rest bindingGroup
  match hFormats : firstMismatchedTemporalFormat? first.format rest with
  | some (path, found) =>
      throw (.mixedDeclaredFormats path found first.format)
  | none => pure { shape, first, rest, oneDeclaredFormat := hFormats }

namespace TemporalValuesNotUniqueElabError

/-- The Kernel diagnostic class this refusal corresponds to, or `none` where this project refuses a shape whose Kernel class it has not established.

`none` is deliberate rather than a placeholder: `missingDeclaredFormat` is this project's own insufficiency for a declaration the Kernel rejects earlier at model level with an unmeasured code, an empty group expansion reaches here only through the unmeasured `RuleGroup` spelling, and a filter failure belongs to the correlation surface. Mapping any of them to a plausible-looking name would assert an unmeasured correspondence. Every shape refusal delegates to the shared checker's own projection, because the star, arity, and duplicate gates do not vary by carrier. -/
def diagnostic? : TemporalValuesNotUniqueElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .inadmissibleKind _ _ => some .onlyStringEnumNumberDateAllowed
  -- The temporal format rule lives inside the same Kernel predicate as the kind gate and reports
  -- its code, which is why a cross-temporal list reports it rather than the mixing code.
  | .mixedDeclaredFormats _ _ _ => some .onlyStringEnumNumberDateAllowed
  | .mixedCategories _ _ => some .varyingTypesNotAllowed
  | .missingDeclaredFormat _ => none
  | .having error => error.diagnostic?
  | .groupExpansionEmpty _ | .incoherentCore => none

end TemporalValuesNotUniqueElabError

/-- Project one addressed temporal cell to its compared identity. The decoded value is deliberately discarded in favour of the exact stored text; empty and formally unavailable cells keep their own states, because this operator skips both alike. -/
def temporalUniquenessCell (cell : CheckedCell) (stored : Option String) :
    ValueListCell .token :=
  match observeCell .validation cell, stored with
  | .value _, some text => .present text
  -- Unreachable for a checked document: a parsed cell has a physical placement and
  -- therefore stored text. Skipping is the conservative projection if it ever were.
  | .value _, none => .empty
  | .empty, _ => .empty
  | .unknown cause, _ | .poison cause, _ => .unknown cause

namespace CheckedTemporalValuesNotUniqueSource

/-- Evaluate the temporal uniqueness predicate from one immutable model-certified checked document. Slots resolve in authored order and every reached cell reaches the scan, because this operator skips a formally unavailable cell instead of suppressing on it. -/
def evaluateCheckedDocumentValuesNotUnique
    (checked : CheckedTemporalValuesNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError Verdict := do
  let tagged ← collectTaggedValueListCells
    (fun operand => do
      match operand with
      | .selected source _ =>
          source.sideWith .validation document.source.toDocument outer (document.computationContextAt outer).read
            (document.computationContextAt outer).storedText document.computationFillContext.read document.storedTextIn
            (document.resolveSemanticIndexColumnWith document.read)
            (fun _ cell stored => pure (temporalUniquenessCell cell stored))
      | _ =>
          let core ← operand.resolveValidationCore (world := world) document outer
          pure {
            cells := core.addressedCells.map (fun addressed => temporalUniquenessCell addressed.cell addressed.stored)
            hasUninstantiatedTail := core.hasUninstantiatedTail
            hasHaving := core.hasHaving
            hasNonRelevant := core.hasNonRelevant })
    checked.operands
  pure (evalValuesNotUniqueVerdict tagged)

end CheckedTemporalValuesNotUniqueSource

end A12Kernel
