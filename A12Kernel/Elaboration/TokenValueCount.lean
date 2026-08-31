import A12Kernel.Elaboration.BooleanValueCount
import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked textual value counts

This consumer applies the common checked String/Enumeration entity list to `NumberOfValueInFields`. Its authored slots retain direct stored/category identity, while the decoded String constant is unrestricted for String fields and must belong to every selected Enumeration projection's exact domain. The generic value-count fold owns exact token equality and filter-sensitive movement; this module owns only its projection-bearing surface, static token-family admission, and phase-specific entity-list traversal.
-/

namespace A12Kernel

/-- Compatibility name for the shared projection-bearing token slot. -/
abbrev SurfaceTokenValueCountOperand :=
  SurfaceProjectedTokenEntityOperand

/-- Compatibility name for the shared projection-bearing token entity list. -/
abbrev SurfaceTokenValueCountSource :=
  SurfaceProjectedTokenEntitySource

/-- The measured full-validation authoring form with one terminal repeatable starred group as the whole value-count operand. -/
structure SurfaceTokenValueCountStarredGroupValidationSource where
  group : SurfaceStarGroupPath
  deriving Repr, DecidableEq

/-- The same measured surface is now admitted by checked computation without replacing the established validation constructor namespace. -/
abbrev SurfaceTokenValueCountStarredGroupSource :=
  SurfaceTokenValueCountStarredGroupValidationSource

/-- The measured full-validation authoring form with one fixed nonrepeatable path group as the whole value-count operand. Keeping the ordinary group path exact excludes the separately unmeasured `RuleGroup` form. -/
structure SurfaceTokenValueCountFixedGroupValidationSource where
  group : SurfaceGroupPath
  deriving Repr, DecidableEq

/-- String accepts every decoded literal; Enumeration requires membership in its exact selected stored/category domain. The gate reads one declaration beside the operand resolved from it, which is what lets a direct slot, a starred slot, and one member of a group expansion share it. -/
def FlatFieldDecl.allowsTokenValueCountLiteral (declaration : FlatFieldDecl)
    (operand : FlatTextFieldOperand) (expected : String) : Bool :=
  match operand with
  | .string _ => true
  | .enumeration source =>
      match declaration.enumeration with
      | some enumeration =>
          match source.projection with
          | .stored => enumeration.storedTokens.contains expected
          | .category mapping => mapping.categoryTokens.contains expected
      | none => false

namespace CheckedTokenField

def allowsValueCountLiteral (checked : CheckedTokenField model)
    (expected : String) : Bool :=
  checked.declaration.allowsTokenValueCountLiteral checked.operand expected

end CheckedTokenField

namespace CheckedTokenStarSource

/-- Starred token operands retain the same declaration-owned literal gate as direct operands. -/
def allowsValueCountLiteral (checked : CheckedTokenStarSource model)
    (expected : String) : Bool :=
  checked.source.declaration.allowsTokenValueCountLiteral checked.operand
    expected

end CheckedTokenStarSource

namespace CheckedTokenEntityOperand

def path : CheckedTokenEntityOperand model → List String
  | .field source => source.declaration.path
  | .star source => source.source.declaration.path
  | .group source => source.groupPath

/-- A group slot admits the literal only when **every** expanded declaration does, which is the same all-slots rule the whole list already applies one level up. The measured starred String group does not discriminate this gate because every String literal is admitted; applying it to Enumeration declarations remains the representation's internally executable choice. -/
def allowsValueCountLiteral (checked : CheckedTokenEntityOperand model)
    (expected : String) : Bool :=
  match checked with
  | .field source => source.allowsValueCountLiteral expected
  | .star source => source.allowsValueCountLiteral expected
  | .group source =>
      source.slots.all fun slot =>
        slot.declaration.allowsTokenValueCountLiteral slot.operand expected

def directField? : CheckedTokenEntityOperand model →
    Option (CheckedTokenField model)
  | .field source => some source
  | .star _ | .group _ => none

end CheckedTokenEntityOperand

namespace CheckedTokenEntitySource

def allowsValueCountLiteral (checked : CheckedTokenEntitySource model)
    (expected : String) : Bool :=
  checked.operands.all (fun operand =>
    operand.allowsValueCountLiteral expected)

def directFields? (checked : CheckedTokenEntitySource model) :
    Option (List (CheckedTokenField model)) :=
  checked.operands.mapM CheckedTokenEntityOperand.directField?

end CheckedTokenEntitySource

inductive TokenValueCountElabError where
  | source (error : TokenEntityElabError)
  | literalOutsideEnumerationDomain (path : List String) (literal : String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked typed token count. The literal is retained with the complete source and its all-Enumeration domain certificate. -/
structure CheckedTokenValueCountSource (model : FlatModel) where
  expected : String
  source : CheckedTokenEntitySource model
  expectedAllowed : source.allowsValueCountLiteral expected = true

/-- One checked whole-group token count. The dedicated carrier proves that runtime owns exactly one group extent, so its computation projection can narrow capacity without widening direct, star, or filtered computation. -/
structure CheckedTokenValueCountGroupSource (model : FlatModel) where
  expected : String
  starredSource : CheckedStarredGroupSource model
  group : CheckedTokenEntityGroup model
  sourceOwned : group.source = .starred starredSource
  modelWellFormed : model.validate.isOk = true
  expectedAllowed :
    (CheckedTokenEntityOperand.group group).allowsValueCountLiteral expected = true

namespace CheckedTokenValueCountSource

/-- Every typed value count has the kernel's fixed integral result scale. -/
def scaleSummary (_checked : CheckedTokenValueCountSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField (checked : CheckedTokenValueCountSource model)
    (field : FieldId) : Bool :=
  checked.source.referencesField field

end CheckedTokenValueCountSource

namespace CheckedTokenValueCountGroupSource

def scaleSummary (_checked : CheckedTokenValueCountGroupSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField (checked : CheckedTokenValueCountGroupSource model)
    (field : FieldId) : Bool :=
  checked.group.referencesField field

/-- Recover the established general checked source for validation consumers without exposing group computation on its direct, starred-field, or filtered variants. -/
def toCheckedTokenValueCountSource
    (checked : CheckedTokenValueCountGroupSource model) :
    CheckedTokenValueCountSource model :=
  let source : CheckedTokenEntitySource model := {
    first := .group checked.group
    rest := []
    modelWellFormed := checked.modelWellFormed
    requiredMultiplicity := by rfl
    uniqueDirectOperands := by rfl }
  { expected := checked.expected
    source
    expectedAllowed := by
      simpa [source, CheckedTokenEntitySource.allowsValueCountLiteral,
        CheckedTokenEntitySource.operands] using checked.expectedAllowed }

end CheckedTokenValueCountGroupSource

/-- Retain a decoded literal beside a checked token source after certifying every selected String/Enumeration domain. -/
private def finishTokenValueCountSource (expected : String)
    (source : CheckedTokenEntitySource model) :
    Except TokenValueCountElabError (CheckedTokenValueCountSource model) := do
  if hAllowed : source.allowsValueCountLiteral expected = true then
    pure { expected, source, expectedAllowed := hAllowed }
  else
    match source.operands.find? fun operand =>
        !operand.allowsValueCountLiteral expected with
    | some operand =>
        throw (.literalOutsideEnumerationDomain operand.path expected)
    | none => throw .incoherentCore

/-- Resolve the projection-bearing entity-list shape, certify String/Enumeration membership, and reject the first selected-domain mismatch in authored order. -/
def elaborateTokenValueCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : String)
    (authored : SurfaceTokenValueCountSource) :
    Except TokenValueCountElabError (CheckedTokenValueCountSource model) := do
  let source ← elaborateProjectedTokenEntitySource model declaringGroup authored
    |>.mapError .source
  finishTokenValueCountSource expected source

private theorem certifiedStarredTokenEntityGroup_source
    (starred : CheckedStarredGroupSource model)
    (group : CheckedTokenEntityGroup model)
    (certified : certifyTokenEntityGroup model (.starred starred) = .ok group) :
    group.source = .starred starred := by
  unfold certifyTokenEntityGroup at certified
  split at certified
  · split at certified
    · contradiction
    · cases certified
      rfl
  · contradiction

private def certifyStarredTokenValueCountGroup
    (model : FlatModel) (starred : CheckedStarredGroupSource model) :
    Except TokenEntityGroupError
      { group : CheckedTokenEntityGroup model //
        group.source = .starred starred } :=
  match certified : certifyTokenEntityGroup model (.starred starred) with
  | .error error => .error error
  | .ok group =>
      .ok ⟨group,
        certifiedStarredTokenEntityGroup_source starred group certified⟩

/-- Resolve the measured form with one terminal repeatable starred group and retain the exact whole-group carrier used by validation and computation. -/
def elaborateTokenValueCountStarredGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : String)
    (authored : SurfaceTokenValueCountStarredGroupSource) :
    Except TokenValueCountElabError
      (CheckedTokenValueCountGroupSource model) := do
  let starred ← elaborateStarredGroupSource model declaringGroup authored.group
    |>.mapError fun error => .source (.shape (.starredGroup error))
  let checkedGroup ← certifyStarredTokenValueCountGroup model starred
    |>.mapError fun error => .source (.group error)
  let group := checkedGroup.1
  if hAllowed : CheckedTokenEntityOperand.allowsValueCountLiteral
      (.group group) expected = true then
    pure {
      expected
      starredSource := starred
      group
      sourceOwned := checkedGroup.2
      modelWellFormed := starred.modelWellFormed
      expectedAllowed := hAllowed }
  else
    throw (.literalOutsideEnumerationDomain group.groupPath expected)

/-- Compatibility entry point preserving the established general checked validation carrier. -/
def elaborateTokenValueCountStarredGroupValidationSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : String)
    (authored : SurfaceTokenValueCountStarredGroupValidationSource) :
    Except TokenValueCountElabError (CheckedTokenValueCountSource model) :=
  (elaborateTokenValueCountStarredGroupSource
    model declaringGroup expected authored).map
      CheckedTokenValueCountGroupSource.toCheckedTokenValueCountSource

/-- Resolve the measured full-validation-only form with one fixed nonrepeatable path group through the common token entity-list gates. -/
def elaborateTokenValueCountFixedGroupValidationSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : String)
    (authored : SurfaceTokenValueCountFixedGroupValidationSource) :
    Except TokenValueCountElabError (CheckedTokenValueCountSource model) := do
  let source ← elaborateTokenEntitySource model declaringGroup {
    first := .group (.path authored.group)
    rest := [] }
    |>.mapError .source
  finishTokenValueCountSource expected source

namespace CheckedTokenValueCountGroupSource

/-- Full validation classifies the group's **in-capacity** extent through each declaration's retained
token projection, exactly as this carrier's computation arm already did.

    The two arms were split here on an untested reading that full validation retained the over-limit
    cell and reported its formal cause. It does not: on a document whose only match sits one index
    above capacity, kernel 30.8.1 answers `0`, and on a document whose only *malformed* cell sits
    there the aggregate still evaluates, while the identical cell one index lower makes it
    non-evaluable ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-starred-group-operand-extent)).
    The over-repetition findings stay on the immutable checked document either way. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedTokenValueCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  let resolved ← (CheckedTokenEntityOperand.group checked.group)
    |>.resolveCheckedValidationOperand document outer
  let side := (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
    |>.appendResolved (resolved.inCapacityValueListSideAt .validation)
  pure (evalValueCountAggregate checked.expected side)

/-- Computation excludes cells beneath a declared-capacity violation before classifying group content, leaving their structural findings on the checked document. -/
def evaluateCheckedDocumentComputation
    (checked : CheckedTokenValueCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  let resolved ← (CheckedTokenEntityOperand.group checked.group)
    |>.resolveCheckedValidationOperand document outer
  let side := (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
    |>.appendResolved (resolved.inCapacityValueListSideAt .computation)
  pure (evalValueCountAggregate checked.expected side)

end CheckedTokenValueCountGroupSource

namespace CheckedTokenEntityOperand

/-- Resolve one token slot at computation phase. Filtered stars reuse the shared one-kept-successor traversal and retain per-slot filter provenance for the value-count fold.

    A group slot refuses: this route reads through caller-supplied functions over a raw `Document`, which cannot answer which rows of the group's subtree exist, and computation over a group extent has no retained observation behind it either. -/
def resolvedValueCountComputationSide
    (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) NumericOperand) :=
  match checked with
  | .group source => .error (.unsupportedGroupOperand source.groupPath)
  | .field source =>
      pure (.inl (source.resolvedSideAt .computation directRead))
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      match source.filter with
      | none =>
          pure (.inl (resolved.toResolvedSide
            (source.valueListCellAt .computation starRead)))
      | some having =>
          let filterContext : CorrelationContext := { read := filterRead }
          let consume := fun cells environment =>
            match source.valueListCellAt .computation starRead environment with
            | .unknown cause => .inr cause
            | cell => .inl (cell :: cells)
          match having.condition.scanComputation filterContext outer consume
              resolved.environments [] with
          | .exhausted reversed =>
              pure (.inl {
                cells := reversed.reverse
                hasUninstantiatedTail := resolved.domain.hasOpenTail
                hasHaving := true })
          | .terminated cause | .poison cause =>
              pure (.inr (.unknown cause))

end CheckedTokenEntityOperand

namespace CheckedTokenValueCountSource

/-- Evaluate a direct-only checked token count without inventing repeatable topology. -/
def evaluateDirectAt? (checked : CheckedTokenValueCountSource model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    Option NumericOperand := do
  let fields ← checked.source.directFields?
  let side := fields.foldl (fun accumulated field =>
    accumulated.appendResolved (field.resolvedSideAt phase read))
    (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
  pure (evalValueCountAggregate checked.expected side)

/-- Full validation preserves authored slot order, exact token classification, omitted tails, and per-filter selected-match provenance. -/
def evaluateValidation (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evalResolvedValueCountOperands
    checked.expected checked.source.operands fun operand => do
      pure (.inl (← operand.resolvedValidationSide document outer
        directRead starRead))

/-- Full validation over the immutable checked document reuses the shared addressed token operand and retains per-slot filter provenance for the existing value-count fold.

    A group slot narrows to its declared-capacity extent, starred or not: kernel 30.8.1 answers `0`
    for `NumberOfValueInFields("KEEP" In G)` when the only matching cell sits beyond its group's
    declared repeatability, and `1` on the control one index lower
    ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep)).
    The starred form answers the same way on its own
    [probe](../../docs/sources/group-and-iteration-probes.md#src-starred-group-operand-extent). -/
def evaluateCheckedDocumentValidation
    (checked : CheckedTokenValueCountSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  evalResolvedValueCountOperands
    checked.expected checked.source.operands fun operand => do
      let resolved ←
        operand.resolveCheckedValidationOperand document outer
      match operand with
      | .group _ =>
          pure (.inl (resolved.inCapacityValueListSideAt .validation))
      | .field _ | .star _ =>
          pure (.inl (resolved.valueListSideAt .validation))

/-- Computation shares the same checked source and count fold while each filtered slot uses the computation iterator's one-kept-successor traversal. -/
def evaluateComputation (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evalResolvedValueCountOperands
    checked.expected checked.source.operands fun operand =>
      operand.resolvedValueCountComputationSide document outer directRead
        filterRead starRead

/-- Partial validation skips any filtered rule before topology or reads; otherwise it uses the local existential value-list account matching the measured numeric outcome pattern and reuses the same count fold. -/
def evaluatePartialValidation
    (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationAggregateResult :=
  if checked.source.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedValueCountSide .token)
        (terminal := PartialValidationAggregateResult)
        (fun operand => operand.resolvedPartialValueCountSide document outer
          scope directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.appendResolved side)
        checked.source.operands .empty with
    | .inl side =>
        pure (.evaluated (evalValueCountAggregate checked.expected side))
    | .inr result => pure result

end CheckedTokenValueCountSource

end A12Kernel
