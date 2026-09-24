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

/-- Evaluate the measured full-validation group extent with the existing empty/filled/formal-invalid count semantics. This returns the count only; comparison movement for a group source remains outside until a non-vacuous polarity observation fixes it.

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
    Except CheckedAddressingError FilledFieldCount := do
  let resolved ← document.resolveCheckedGroupEntityOperandCore outer
    checked.source.boundLevelCount checked.declarations
  pure (numberOfFilledFields
    (resolved.inCapacityAddressedCells.map fun addressed =>
      observeCell .validation addressed.cell))

/-- Lift the validation count against the operand's declared **slot capacity**, so the count stays
    grow-only until every slot the operand can reach is filled.

    A fixed group's capacity is its subtree's: a repeatable descendant admits more cells than the
    subtree declares fields, and the declaration count would freeze the count early
    ([checkpoint](../../docs/SOURCES.md#src-filled-field-count-nested-capacity)). A fixed group below
    a starred level also multiplies in every level the star reopens, since kernel 30.8.1 types
    `Rows*/Detail` `VALUE` only once both of Detail's fields are filled in both rows `Rows` admits
    ([checkpoint](../../docs/SOURCES.md#src-below-star-group-runtime)).
    A terminal repeatable star has no movement measurement on this carrier and returns `none`, as
    does an unretained maximum, which no authorable model reaches. -/
def evaluateCheckedDocumentValidationOperand?
    (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option NumericOperand) := do
  let count ← checked.evaluateCheckedDocumentValidation document outer
  let capacity? := match checked.source with
    | .fixed _ => model.groupSubtreeSlotCapacity? checked.source.groupPath
    | .starredPresence _ =>
        model.declarationsSlotCapacity? checked.source.boundLevelCount checked.declarations
    | .starred _ => none
  pure (capacity?.bind fun capacity => (count.availableWithFillability? capacity).map
    fun available => .value available.1 available.2)

/-- The extensional validation tally of the group operand's in-capacity extent.

    `uninstantiated` is `0` because the resolved group core enumerates instantiated rows only.
    The field-fill evaluator supplies the declared tail separately; counting a formally unknown
    instantiated cell as missing would turn the undecided all-full case into a false omission. -/
def validationFillTally (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ValidationFillTally := do
  let resolved ← document.resolveCheckedGroupEntityOperandCore outer
    checked.source.boundLevelCount checked.declarations
  pure (resolved.inCapacityAddressedCells.foldl (init := ({ filled := 0, empty := 0, unknown := 0, uninstantiated := 0 } : ValidationFillTally))
    fun tally addressed =>
      tally.combine (observeCell .validation addressed.cell).asValidationFillTally)

/-- Answer a field-fill operator over the group operand's in-capacity extent and declared tail.

    This is not a projection of `evaluateCheckedDocumentValidation`: the count is unavailable as soon
    as one operand cell is formally invalid, while `AtLeastOneFieldFilled` still fires on a filled
    sibling. The two carriers therefore disagree on a document holding both, deliberately.

    The declared-range predicates require retained maxima below the source's own binding depth,
    so an unretained maximum returns `none`, distinct from an evaluated false-or-unknown result.
    The other four predicates require no capacity and preserve their instantiated-only account
    ([group-fill checkpoint](../../docs/SOURCES.md#src-group-field-fill-declared-slots)). -/
def evaluateCheckedDocumentValidationFill?
    (checked : CheckedFilledFieldCountGroupSource model)
    (operator : FieldFillQuantifier)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option ValidationFillOutcome) := do
  let tally ← checked.validationFillTally document outer
  match operator with
  | .allFieldsFilled | .notAllFieldsFilled | .fieldsNotCollectivelyFilled =>
      pure ((model.declarationsSlotCapacity? checked.source.boundLevelCount
        checked.declarations).map fun capacity =>
          operator.evalValidation { tally with
            uninstantiated := capacity - (tally.filled + tally.empty + tally.unknown) })
  | .noFieldFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
      | .notExactlyOneFieldFilled => pure (some (operator.evalValidation tally))

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
