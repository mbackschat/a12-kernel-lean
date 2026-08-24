import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Checked group-scope filled-field counts

This boundary admits only the two measured whole-operand group forms of `NumberOfFilledFields`: one fixed nonrepeatable ordinary path group or one terminal repeatable starred group. It reuses the shared group extent and the existing validation count, while computation, mixed lists, filters, partial validation, and raw-document execution remain outside.
-/

namespace A12Kernel

structure SurfaceFilledFieldCountFixedGroupValidationSource where
  group : SurfaceGroupPath
  deriving Repr, DecidableEq

structure SurfaceFilledFieldCountStarredGroupValidationSource where
  group : SurfaceStarGroupPath
  deriving Repr, DecidableEq

inductive FilledFieldCountGroupElabError where
  | shape (error : FieldEntityShapeElabError)
  | rootGroup (path : GroupPath)
  | emptyGroup (path : GroupPath)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked group operand and its complete nonempty recursive declaration expansion. No kind certificate is needed because `NumberOfFilledFields` observes placement and formal validity across every field kind. -/
structure CheckedFilledFieldCountGroupSource (model : FlatModel) where
  source : CheckedEntityGroupSource model
  first : FlatFieldDecl
  rest : List FlatFieldDecl
  expansionOwned : model.groupSubtreeFields source.groupPath = first :: rest

namespace CheckedFilledFieldCountGroupSource

def declarations (checked : CheckedFilledFieldCountGroupSource model) :
    List FlatFieldDecl :=
  checked.first :: checked.rest

/-- Evaluate the measured full-validation group extent with the existing empty/filled/formal-invalid count semantics. This returns the count only; comparison movement for a group source remains outside until a non-vacuous polarity observation fixes it. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError FilledFieldCount := do
  let resolved ← document.resolveCheckedGroupEntityOperandCore outer
    checked.source.boundLevelCount checked.declarations
  pure (numberOfFilledFields (resolved.addressedCells.map fun addressed =>
    observeCell .validation addressed.cell))

end CheckedFilledFieldCountGroupSource

private def finishFilledFieldCountGroupSource (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except FilledFieldCountGroupElabError
      (CheckedFilledFieldCountGroupSource model) :=
  if source.groupPath.length == 1 then
    throw (.rootGroup source.groupPath)
  else
    match hExpansion : model.groupSubtreeFields source.groupPath with
    | [] => throw (.emptyGroup source.groupPath)
    | first :: rest => pure { source, first, rest, expansionOwned := hExpansion }

/-- Admit one measured fixed nonrepeatable ordinary path group through the shared entity-list shape gates. -/
def elaborateFilledFieldCountFixedGroupValidationSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceFilledFieldCountFixedGroupValidationSource) :
    Except FilledFieldCountGroupElabError
      (CheckedFilledFieldCountGroupSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup {
    first := .group (.path authored.group)
    rest := [] }
    |>.mapError .shape
  match shape.first with
  | .group reference =>
      finishFilledFieldCountGroupSource model (.fixed reference)
  | _ => throw .incoherentCore

/-- Admit one measured terminal repeatable starred group without admitting the separate starred-ancestor/nonrepeatable-terminal shape. -/
def elaborateFilledFieldCountStarredGroupValidationSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceFilledFieldCountStarredGroupValidationSource) :
    Except FilledFieldCountGroupElabError
      (CheckedFilledFieldCountGroupSource model) := do
  let starred ← elaborateStarredGroupSource model declaringGroup authored.group
    |>.mapError fun error => .shape (.starredGroup error)
  finishFilledFieldCountGroupSource model (.starred starred)

end A12Kernel
