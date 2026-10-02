import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.FieldFillQuantifier
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.NumericComparison

/-! # Checked group-scope filled-field counts

This boundary admits two whole-operand group forms for the count and seven field-fill quantifiers: one fixed nonrepeatable ordinary path group or one starred group, whose terminal is repeatable or a nonrepeatable group below a starred level. Declared slots supplement the instantiated extent only for predicates that read the missing tail. Computation, mixed lists, filters, partial validation, and raw-document execution remain outside.
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

/-- The validation observation of every cell in the operand's in-capacity extent, the one stream the
    count, the tally and an entity list holding this operand all read. -/
def observations (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (List CellObservation) := do
  let resolved ← document.resolveCheckedGroupEntityOperandCore outer
    checked.source.boundLevelCount checked.declarations
  pure (resolved.inCapacityAddressedCells.map fun addressed => observeCell .validation addressed.cell)

/-- Evaluate the measured full-validation group extent with the existing empty/filled/formal-invalid count semantics. This returns the count only; `CheckedFieldFillList.evaluateCountOperand?` adds its movement against `countCapacity?`.

    The domain is the **in-capacity** projection, opted into here exactly as the starred carrier's
    measured consumers opt into it. A cell in a row beyond the group's declared repeatability is not
    counted and does not make the count unknown: on a document whose in-capacity rows are
    instantiated and empty and whose only filled cell lies beyond capacity, kernel 30.8.1 answers
    `0` and fires a `< 1` rule, which an unknown count would leave silent
    ([checkpoint](../../docs/SOURCES.md#src-group-operand-over-limit-extent)). The complete
    formal-cell view stays available on the checked document for the group consumers that have no
    such measurement. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError FilledFieldCount :=
  numberOfFilledFields <$> checked.observations document outer

/-- Lift the validation count against the operand's declared **slot capacity**, so the count stays
    grow-only until every slot the operand can reach is filled.

    A fixed group's capacity is its subtree's: a repeatable descendant admits more cells than the
    subtree declares fields, and the declaration count would freeze the count early
    ([checkpoint](../../docs/SOURCES.md#src-filled-field-count-nested-capacity)). A fixed group below
    a starred level also multiplies in every level the star reopens, since kernel 30.8.1 types
    `Rows*/Detail` `VALUE` only once both of Detail's fields are filled in both rows `Rows` admits
    ([checkpoint](../../docs/SOURCES.md#src-below-star-group-runtime)).
    A terminal repeatable star runs against the same slot capacity: below it the Kernel types an
    `== 0` and an `== 1` member OMISSION and a `> 0` member VALUE, on the
    [starred-extent](../../docs/sources/group-and-iteration-probes.md#src-starred-group-operand-extent)
    and [nested-star](../../docs/sources/group-and-iteration-probes.md#src-nested-star-bound-outer-level)
    captures, read through the population replay on 2026-10-02. No retained row types a starred
    count at capacity. An unretained maximum returns `none`, which no authorable model reaches. -/
def countCapacity? (checked : CheckedFilledFieldCountGroupSource model) : Option Nat :=
  match checked.source with
  | .fixed _ => model.groupSubtreeSlotCapacity? checked.source.groupPath
  | .starredPresence _ | .starred _ =>
      model.declarationsSlotCapacity? checked.source.boundLevelCount checked.declarations

/-- The declared slots the declared-range field-fill predicates read. -/
def fillCapacity? (checked : CheckedFilledFieldCountGroupSource model) : Option Nat :=
  model.declarationsSlotCapacity? checked.source.boundLevelCount checked.declarations

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

/-- Admit one measured fixed nonrepeatable ordinary path group. This carrier opts into the exact
rule-bound scope directly; the shared entity-list resolver stays scalar for its unmeasured token,
Boolean, temporal, and aggregate consumers. -/
def elaborateFilledFieldCountFixedGroupValidationSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceFilledFieldCountFixedGroupValidationSource)
    (writtenGroup : GroupPath := declaringGroup) :
    Except FilledFieldCountGroupElabError
      (CheckedFilledFieldCountGroupSource model) := do
  match model.validate with
  | .error error => throw (.shape (.resolve error))
  | .ok () =>
      let reference ← model.resolveRuleBoundFixedGroupReference declaringGroup
        (.path authored.group) (some writtenGroup)
        |>.mapError fun error => .shape (.groupReference error)
      finishFilledFieldCountGroupSource model (.fixed reference)

/-- Admit one starred group: a repeatable terminal, or a nonrepeatable group below a starred level,
    which the Kernel admits on the count and on all seven field-fill quantifiers
    ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-starred-group-value-count-classes)).
    Either way the operand expands to every field below its terminal with the star carried down, so
    the declared extent below a nonrepeatable terminal is the reopened rows' capacity. -/
def elaborateFilledFieldCountStarredGroupValidationSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceFilledFieldCountStarredGroupValidationSource)
    (writtenGroup : GroupPath := declaringGroup) :
    Except FilledFieldCountGroupElabError
      (CheckedFilledFieldCountGroupSource model) := do
  match ← elaborateStarredGroupOperandSource model declaringGroup authored.group
      |>.mapError fun error =>
        .shape (.starredGroup (error.placeBelowStar model declaringGroup writtenGroup)) with
  | .terminalRepeatable source => finishFilledFieldCountGroupSource model (.starred source)
  | .terminalPresence source => finishFilledFieldCountGroupSource model (.starredPresence source)

end A12Kernel
