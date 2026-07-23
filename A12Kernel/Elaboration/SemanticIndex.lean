import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.SemanticIndex

/-! # Checked one-group Number semantic-index construction

This capsule joins the existing checked one-group raw context to the resolved semantic-index evaluator for one source-grounded profile: a literal Number key selects a Number target in a group with one declared direct-child Number index field. The authored literal is already admitted as a Number value. General raw-token keys, field-valued keys, nested repetitions, and concrete syntax remain outside.
-/

namespace A12Kernel

structure SurfaceNumberSemanticIndex where
  target : SurfaceFieldPath
  /-- The declaration-admitted numeric value of the authored key literal. -/
  key : Rat
  deriving Repr, DecidableEq

inductive SemanticIndexElabError where
  | resolve (error : ResolveError)
  | group (error : SingleGroupElabError)
  | missingIndexField (groupPath : GroupPath)
  | indexFieldNotNumber (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A literal Number semantic-index source certified against one exact target group, index field, and target field in the checked model. -/
structure CheckedNumberSemanticIndexSource (model : FlatModel) where
  group : RepeatableGroupDecl
  indexField : FlatNumberField
  targetField : FlatNumberField
  key : Rat
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  indexDeclared : (group.indexField == some indexField.id) = true
  indexOwned : model.admitsSingleGroupNumber group indexField = true
  targetOwned : model.admitsSingleGroupNumber group targetField = true

/-- Resolve the target first, then require its exact one-level repeatable group and the Number index declaration owned by that group. -/
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
      if hGroup : model.repeatableGroups.contains group = true then
        if hDeclared : group.indexField == some indexField.id then
          if hIndexOwned : model.admitsSingleGroupNumber group indexField = true then
            if hTargetOwned : model.admitsSingleGroupNumber group targetField = true then
              pure {
                group
                indexField
                targetField
                key := authored.key
                modelWellFormed := by rw [hModel]; rfl
                groupOwned := hGroup
                indexDeclared := hDeclared
                indexOwned := hIndexOwned
                targetOwned := hTargetOwned
              }
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
  key : Rat
  row : RowIndex
  deriving Repr, DecidableEq

private structure NumberIndexScan where
  candidates : List NumberIndexCandidate := []
  unavailableKey : Option FormalCause := none
  deriving Repr, DecidableEq

private def NumberIndexScan.noteUnavailable
    (scan : NumberIndexScan) (cause : FormalCause) : NumberIndexScan :=
  match scan.unavailableKey with
  | some _ => scan
  | none => { scan with unavailableKey := some cause }

private def scanNumberIndexKeys (context : SingleGroupValidationContext)
    (indexField : FlatNumberField) : List RowIndex → NumberIndexScan
  | [] => {}
  | row :: remaining =>
      let rest := scanNumberIndexKeys context indexField remaining
      match observeCell .validation (context.read row indexField.id) with
      | .value (.num key) =>
          { rest with candidates := { key, row } :: rest.candidates }
      | .empty => rest.noteUnavailable .required
      | .unknown cause => rest.noteUnavailable cause
      | .value _ | .poison _ => rest.noteUnavailable .malformed

private def NumberIndexCandidate.isDuplicate
    (all : List NumberIndexCandidate) (candidate : NumberIndexCandidate) : Bool :=
  (all.filter fun other => other.key == candidate.key).length > 1

private def NumberIndexScan.toColumn (scan : NumberIndexScan)
    (context : SingleGroupValidationContext) (targetField : FlatNumberField) :
    ResolvedSemanticIndexColumn :=
  let hasDuplicate := scan.candidates.any (NumberIndexCandidate.isDuplicate scan.candidates)
  let unavailableKey := match scan.unavailableKey with
    | some cause => some cause
    | none => if hasDuplicate then some .duplicateIndex else none
  let entries := (scan.candidates.filter fun candidate =>
      !candidate.isDuplicate scan.candidates).map fun candidate =>
        { token := SemanticIndexKey.number candidate.key
          target := context.read candidate.row targetField.id }
  { entries, unavailableKey }

namespace CheckedNumberSemanticIndexSource

/-- Validate row topology, apply declaration-owned key and target checks, remove every duplicate-key participant, and retain one unavailable-column cause. -/
def resolveColumn (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) :
    Except SemanticIndexContextError ResolvedSemanticIndexColumn := do
  raw.validate |>.mapError .topology
  let context := model.checkSingleGroupContext checked.group raw
  pure ((scanNumberIndexKeys context checked.indexField raw.candidates).toColumn
    context checked.targetField)

/-- Evaluate the checked literal Number lookup through the sole resolved phase-policy owner. -/
def lookupValue (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (phase : Phase) :
    Except SemanticIndexContextError CellObservation := do
  let column ← checked.resolveColumn raw
  pure (column.lookupNumberValue phase checked.key)

/-- Project a checked validation read into the established target-declaration-owned Number comparison operand. -/
def validationNumberOperand (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) :
    Except SemanticIndexContextError NumericOperand := do
  let column ← checked.resolveColumn raw
  pure (column.validationNumberKeyOperand checked.targetField.info checked.key)

end CheckedNumberSemanticIndexSource

end A12Kernel
