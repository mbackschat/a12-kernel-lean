import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.RepetitionNotUnique
import A12Kernel.Semantics.SemanticIndex

/-! # Checked one-group Number semantic-index construction

This capsule joins the existing checked flat and one-group raw contexts to the resolved semantic-index evaluator for one source-grounded profile: a literal Number or nonrepeatable Number field selects a Number target in a group with one declared direct-child Number index field. Both key forms use normalized numeric identity; a dynamic field key retains ordinary phase observation before lookup. General raw-token keys, repeatable field-valued keys, nested repetitions, and concrete syntax remain outside.
-/

namespace A12Kernel

inductive SurfaceNumberSemanticIndexKey where
  /-- A declaration-admitted numeric literal value. -/
  | literal (value : Rat)
  /-- A field whose checked current value supplies the lookup key. -/
  | field (reference : SurfaceFieldPath)
  deriving Repr, DecidableEq

structure SurfaceNumberSemanticIndex where
  target : SurfaceFieldPath
  key : SurfaceNumberSemanticIndexKey
  deriving Repr, DecidableEq

inductive SemanticIndexElabError where
  | resolve (error : ResolveError)
  | group (error : SingleGroupElabError)
  | missingIndexField (groupPath : GroupPath)
  | indexFieldNotNumber (path : List String)
  | keyFieldNotNumber (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

inductive CheckedNumberSemanticIndexKey where
  | literal (value : Rat)
  | field (source : FlatNumberField)
  deriving Repr, DecidableEq

namespace CheckedNumberSemanticIndexKey

/-- The dynamic key field must be the exact nonrepeatable Number declaration retained by the checked model. A literal has no additional model owner. -/
def admittedBy (key : CheckedNumberSemanticIndexKey)
    (model : FlatModel) : Bool :=
  match key with
  | .literal _ => true
  | .field source => model.admitsField (.number source)

/-- Apply declaration-owned checking to a dynamic key and retain the requested phase. Literal values bypass the raw context. -/
def observe (key : CheckedNumberSemanticIndexKey) (model : FlatModel)
    (raw : RawFlatContext) (phase : Phase) : CellObservation :=
  match key with
  | .literal value => .value (.num value)
  | .field source => observeCell phase ((model.checkContext raw).read source.id)

end CheckedNumberSemanticIndexKey

/-- A Number semantic-index source certified against one exact target group, index field, target field, and literal or dynamic key in the checked model. -/
structure CheckedNumberSemanticIndexSource (model : FlatModel) where
  group : RepeatableGroupDecl
  indexField : FlatNumberField
  targetField : FlatNumberField
  key : CheckedNumberSemanticIndexKey
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  indexDeclared : (group.indexField == some indexField.id) = true
  indexOwned : model.admitsSingleGroupNumber group indexField = true
  targetOwned : model.admitsSingleGroupNumber group targetField = true
  keyOwned : key.admittedBy model = true

/-- Resolve the target first, then require its exact one-level repeatable group, Number index declaration, and literal or nonrepeatable Number key. -/
def elaborateNumberSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberSemanticIndex) :
    Except SemanticIndexElabError (CheckedNumberSemanticIndexSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let targetDeclaration ← model.resolveFieldDeclarationUnchecked
        declaringGroup authored.target |>.mapError .resolve
      let group ← model.lookupUniqueRepeatablePath targetDeclaration.groupPath
        |>.mapError .resolve
      let (_, targetField) ← model.resolveNumberInGroup
        declaringGroup group authored.target |>.mapError .group
      let indexId ← match group.indexField with
        | some indexId => pure indexId
        | none => throw (.missingIndexField group.path)
      let indexDeclaration ← model.lookupUniqueId indexId |>.mapError .resolve
      let indexField ← match indexDeclaration.toNumberField? with
        | some indexField => pure indexField
        | none => throw (.indexFieldNotNumber indexDeclaration.path)
      let key ← match authored.key with
        | .literal value => pure (.literal value)
        | .field reference =>
            let declaration ← model.resolveNonrepeatableFieldUnchecked
              declaringGroup reference |>.mapError .resolve
            match declaration.toNumberField? with
            | some source => pure (.field source)
            | none => throw (.keyFieldNotNumber declaration.path)
      if hGroup : model.repeatableGroups.contains group = true then
        if hDeclared : group.indexField == some indexField.id then
          if hIndexOwned : model.admitsSingleGroupNumber group indexField = true then
            if hTargetOwned : model.admitsSingleGroupNumber group targetField = true then
              if hKeyOwned : key.admittedBy model = true then
                pure {
                  group
                  indexField
                  targetField
                  key
                  modelWellFormed := by rw [hModel]; rfl
                  groupOwned := hGroup
                  indexDeclared := hDeclared
                  indexOwned := hIndexOwned
                  targetOwned := hTargetOwned
                  keyOwned := hKeyOwned
                }
              else
                throw .incoherentCore
            else
              throw .incoherentCore
          else
            throw .incoherentCore
        else
          throw .incoherentCore
      else
        throw .incoherentCore

inductive SemanticIndexContextError where
  | topology (error : SingleGroupContextError)
  deriving Repr, DecidableEq

private structure NumberIndexCandidate where
  row : RowIndex
  key : RepetitionKeyComponent
  deriving Repr, DecidableEq

private def scanNumberIndexKeys (context : SingleGroupValidationContext)
    (indexField : FlatNumberField) : List RowIndex → List NumberIndexCandidate
  | [] => []
  | row :: remaining =>
      let key := match observeCell .validation (context.read row indexField.id) with
        | .value (.num value) => .present (.number value)
        | .empty => .empty
        | .unknown cause | .poison cause => .unknown cause
        | .value _ => .unknown .malformed
      { row, key } :: scanNumberIndexKeys context indexField remaining

private def NumberIndexCandidate.resolved
    (level : RepeatableLevel) (candidate : NumberIndexCandidate) :
    ResolvedRepetitionKeyRow :=
  { row := [(level, candidate.row)], key := [candidate.key] }

private def NumberIndexCandidate.directUnavailable? :
    NumberIndexCandidate → Option FormalCause
  | { key := .empty, .. } => some .required
  | { key := .unknown cause, .. } => some cause
  | _ => none

private def NumberIndexCandidates.toColumn
    (candidates : List NumberIndexCandidate) (level : RepeatableLevel)
    (context : SingleGroupValidationContext) (targetField : FlatNumberField) :
    ResolvedSemanticIndexColumn :=
  let results := evalRepetitionNotUnique (candidates.map (·.resolved level))
  let unavailableKey := match
      (candidates.filterMap NumberIndexCandidate.directUnavailable?).head? with
    | some cause => some cause
    | none =>
        if results.any fun result => match result.verdict with
          | .fired _ => true
          | _ => false then
          some .duplicateIndex
        else
          none
  let entries := (candidates.zip results).filterMap fun pair =>
    match pair.1.key, pair.2.verdict with
    | .present (.number key), .notFired =>
        some {
          token := SemanticIndexKey.number key
          target := context.read pair.1.row targetField.id
        }
    | _, _ => none
  { entries, unavailableKey }

namespace CheckedNumberSemanticIndexSource

/-- Validate row topology, apply declaration-owned key and target checks, remove every duplicate-key participant, and retain one unavailable-column cause. -/
def resolveColumn (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) :
    Except SemanticIndexContextError ResolvedSemanticIndexColumn := do
  raw.validate |>.mapError .topology
  let context := model.checkSingleGroupContext checked.group raw
  pure (NumberIndexCandidates.toColumn
    (scanNumberIndexKeys context checked.indexField raw.candidates)
    checked.group.level context checked.targetField)

/-- Evaluate the checked literal or dynamic Number lookup through the sole resolved phase-policy owner. -/
def lookupValue (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (keyRaw : RawFlatContext) (phase : Phase) :
    Except SemanticIndexContextError CellObservation := do
  let column ← checked.resolveColumn raw
  let key := checked.key.observe model keyRaw phase
  pure (column.lookupNumberObservation phase key)

/-- Project a checked validation read into the established target-declaration-owned Number comparison operand. -/
def validationNumberOperand (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (keyRaw : RawFlatContext) :
    Except SemanticIndexContextError NumericOperand := do
  let column ← checked.resolveColumn raw
  let key := checked.key.observe model keyRaw .validation
  pure (column.validationNumberObservedKeyOperand checked.targetField.info key)

end CheckedNumberSemanticIndexSource

end A12Kernel
