import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.FieldFillQuantifier
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.NumericComparison

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

/-- Evaluate the measured full-validation group extent with the existing empty/filled/formal-invalid count semantics. This returns the count only; comparison movement for a group source remains outside until a non-vacuous polarity observation fixes it.

    The domain is the **in-capacity** projection, opted into here exactly as the starred carrier's
    measured consumers opt into it. A cell in a row beyond the group's declared repeatability is not
    counted and does not make the count unknown: on a document whose in-capacity rows are
    instantiated and empty and whose only filled cell lies beyond capacity, kernel 30.8.1 answers
    `0` and fires a `< 1` rule, which an unknown count would leave silent
    ([checkpoint](../../../docs/SOURCES.md#src-group-operand-over-limit-extent)). The complete
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

/-- The field-fill operators a **group** operand can answer here.

    Three of the seven read a declared-but-uninstantiated slot count, and the group operand's
    resolved core enumerates instantiated rows only, so `AllFieldsFilled`, `NotAllFieldsFilled`, and
    `FieldsNotCollectivelyFilled` would each be answered from a tally that silently reports zero
    uninstantiated slots where a declared repeatable tail exists. They are excluded rather than
    answered wrongly; `checkedFilledFieldCountGroupSource_tally_uninstantiated_zero` states the
    quantity that makes the exclusion necessary rather than cautious.

    The four admitted operators read only `filled` and `unknown`, which the instantiated extent
    supplies exactly. `NoFieldFilled` and `AtLeastOneFieldFilled` are Kernel-measured
    ([checkpoint](../../../docs/SOURCES.md#src-group-operand-over-limit-extent)); the other two are
    the same mechanism at a different threshold and remain external evidence pending. -/
inductive GroupFieldFillQuantifier where
  | noFieldFilled
  | atLeastOneFieldFilled
  | moreThanOneFieldFilled
  | notExactlyOneFieldFilled
  deriving Repr, DecidableEq

/-- Every admitted group operator is the ordinary field-fill operator of the same name; the subset is
an admission boundary, not a second semantics. -/
def GroupFieldFillQuantifier.toFieldFillQuantifier :
    GroupFieldFillQuantifier → FieldFillQuantifier
  | .noFieldFilled => .noFieldFilled
  | .atLeastOneFieldFilled => .atLeastOneFieldFilled
  | .moreThanOneFieldFilled => .moreThanOneFieldFilled
  | .notExactlyOneFieldFilled => .notExactlyOneFieldFilled

/-- Lift the measured fixed-group validation count against its subtree's declared **slot capacity**.
    A subtree owning a repeatable descendant admits more cells than it declares fields, and the count
    stays grow-only until every one of those slots is filled; the declaration count would freeze it
    early ([checkpoint](../../../docs/SOURCES.md#src-filled-field-count-nested-capacity)). An
    unretained descendant maximum yields no operand at all rather than an unmeasured movement rule,
    matching the starred carrier and reachable in no authorable model. The starred carrier returns
    `none` here because its movement depends on a separate declared row extent. -/
def evaluateCheckedDocumentFixedValidationOperand?
    (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option NumericOperand) := do
  let count ← checked.evaluateCheckedDocumentValidation document outer
  match checked.source with
  | .fixed _ =>
      pure ((model.groupSubtreeSlotCapacity? checked.source.groupPath).bind
        fun capacity => (count.availableWithFillability? capacity).map
          fun available => .value available.1 available.2)
  | .starred _ | .starredPresence _ => pure none

/-- The extensional validation tally of the group operand's in-capacity extent.

    `uninstantiated` is `0` because the resolved group core enumerates instantiated rows only. That
    is a fact about this extent rather than about the model, which is exactly why the three
    tail-reading operators are outside `GroupFieldFillQuantifier`. -/
def validationFillTally (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ValidationFillTally := do
  let resolved ← document.resolveCheckedGroupEntityOperandCore outer
    checked.source.boundLevelCount checked.declarations
  pure (resolved.inCapacityAddressedCells.foldl (init := ({ filled := 0, empty := 0, unknown := 0, uninstantiated := 0 } : ValidationFillTally))
    fun tally addressed =>
      tally.combine (observeCell .validation addressed.cell).asValidationFillTally)

/-- Answer one admitted field-fill operator over the group operand's in-capacity extent.

    This is not a projection of `evaluateCheckedDocumentValidation`: the count is unavailable as soon
    as one operand cell is formally invalid, while `AtLeastOneFieldFilled` still fires on a filled
    sibling. The two carriers therefore disagree on a document holding both, deliberately. -/
def evaluateCheckedDocumentValidationFill
    (checked : CheckedFilledFieldCountGroupSource model)
    (operator : GroupFieldFillQuantifier)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ValidationFillOutcome := do
  let tally ← checked.validationFillTally document outer
  pure (operator.toFieldFillQuantifier.evalValidation tally)

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
    (authored : SurfaceFilledFieldCountFixedGroupValidationSource) :
    Except FilledFieldCountGroupElabError
      (CheckedFilledFieldCountGroupSource model) := do
  match model.validate with
  | .error error => throw (.shape (.resolve error))
  | .ok () =>
      let reference ← model.resolveRuleBoundFixedGroupReference declaringGroup
        (.path authored.group) |>.mapError fun error => .shape (.groupReference error)
      finishFilledFieldCountGroupSource model (.fixed reference)

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
