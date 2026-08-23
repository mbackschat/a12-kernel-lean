import A12Kernel.Elaboration.DateRangeOverlap

/-! # Checked plural DateRange overlap

This boundary owns static admission and checked-document assembly for `AtLeastOneDateRangeOverlaps`,
the genuinely scalar-versus-list overlap operator. It is separate from the any-pair singular operator
because the two retain different sources, different refusal classes, and a different scan: the scalar
is resolved first and an unusable scalar leaves every list operand unread. Shared certification,
the uniform-year gate, and pure overlap truth stay with their owners in
`A12Kernel.Elaboration.DateRangeOverlap` and `A12Kernel.Semantics.DateRangeOverlapOperators`.
-/

namespace A12Kernel

/-! ## Checked `AtLeastOneDateRangeOverlaps` source admission -/

inductive DateRangeOverlapSourceRole where
  | scalar
  | list
  deriving Repr, DecidableEq

/-- Static refusal while certifying the plural scalar-versus-list DateRange overlap source. -/
inductive AtLeastOneDateRangeOverlapsElabError where
  | shape (error : FieldEntityShapeElabError)
  | scalarStarred (path : List String)
  | scalarFilteredStarred (path : List String)
  | scalarGroup (path : GroupPath)
  | measuredNumberPairNotDateRange (scalarPath listPath : List String)
  | sourceNotDateRange (role : DateRangeOverlapSourceRole)
      (path : List String) (actual : SurfaceScalarKind)
  | unsupportedPolicy (role : DateRangeOverlapSourceRole)
      (path : List String) (format separator : String)
  | unsupportedReadForm (role : DateRangeOverlapSourceRole)
      (path : List String) (form : FieldEntityReadForm)
  | groupExpansionEmpty (path : GroupPath)
  | groupExpansionNotDateRange (path : GroupPath)
  | dateWithAndWithoutYear
  | yearInterpretationNotSupported (role : DateRangeOverlapSourceRole)
      (path : List String)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace AtLeastOneDateRangeOverlapsElabError

/-- Project only the two exact operator-specific diagnostic rows plus the shared shape classes. Every other local refusal remains deliberately unmapped. -/
def diagnostic? : AtLeastOneDateRangeOverlapsElabError →
    Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .scalarStarred _ => some .invalidParameterForDateRangeComparison
  | .measuredNumberPairNotDateRange _ _ => some .noDateRange
  | .dateWithAndWithoutYear => some .dateWithAndWithoutYear
  | .yearInterpretationNotSupported _ _ => some .invalidDateRangeFormat
  | .scalarFilteredStarred _ | .scalarGroup _ |
      .sourceNotDateRange _ _ _ | .unsupportedPolicy _ _ _ _ |
      .unsupportedReadForm _ _ _ | .groupExpansionEmpty _ |
      .groupExpansionNotDateRange _ | .having _ | .incoherentCore => none

end AtLeastOneDateRangeOverlapsElabError

/-- One group-scope list slot whose complete recursive expansion is nonempty and uses the supported DateRange policies. -/
structure CheckedDateRangeEntityGroup (model : FlatModel) where
  source : CheckedEntityGroupSource model
  first : CheckedCanonicalDateRangeField
  rest : List CheckedCanonicalDateRangeField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      (fun declaration => (certifyCanonicalDateRangeField declaration).toOption) =
        first :: rest
  expansionAllDateRange :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration =>
        (certifyCanonicalDateRangeField declaration).toOption.isSome) = true

/-- One certified list-side field, star, or recursively expanded group operand. -/
inductive CheckedAtLeastOneDateRangeOverlapsListOperand (model : FlatModel) where
  | field (source : CheckedSingularDateRangesOverlapOperand model)
  | group (source : CheckedDateRangeEntityGroup model)

namespace CheckedAtLeastOneDateRangeOverlapsListOperand

def hasHaving : CheckedAtLeastOneDateRangeOverlapsListOperand model → Bool
  | .field source => source.hasHaving
  | .group _ => false

/-- Whether every declaration this operand retains has a supported policy. A group operand expands only through the exact canonical certification, so its whole expansion is exact. -/
def policySupported : CheckedAtLeastOneDateRangeOverlapsListOperand model → Bool
  | .field source => source.policySupported
  | .group source =>
      (source.first :: source.rest).all fun field =>
        (DateRangeFormat.ofPolicy? field.policy).isSome

/-- The declarations this operand contributes, in the operand's own order. -/
def fields : CheckedAtLeastOneDateRangeOverlapsListOperand model →
    List FlatFieldDecl
  | .field source => [source.declaration]
  | .group source => (source.first :: source.rest).map (·.declaration)

end CheckedAtLeastOneDateRangeOverlapsListOperand

/-- Parser-independent scalar-versus-list source. The scalar retains the broad entity spelling long enough to project the measured starred-scalar diagnostic; checked construction narrows it to one direct field. -/
structure SurfaceAtLeastOneDateRangeOverlapsSource where
  scalar : SurfaceFieldEntityOperand
  list : SurfaceFieldEntitySource
  deriving Repr, DecidableEq

/-- One certified plural scalar: the canonical exact policy, or one direct fragment profile the checked model resolves. The scalar is always a direct stored field, so it needs no star or group arm. -/
inductive CheckedAtLeastOneDateRangeOverlapsScalar (model : FlatModel) where
  | canonical (source : CheckedCanonicalDateRangeField)
  | fragmentField (source : CheckedDirectDateRangeOverlapFragmentField model)

namespace CheckedAtLeastOneDateRangeOverlapsScalar

/-- The authored declaration behind the scalar. -/
def declaration : CheckedAtLeastOneDateRangeOverlapsScalar model → FlatFieldDecl
  | .canonical source => source.declaration
  | .fragmentField source => source.declaration

/-- Whether the retained scalar declaration satisfies the exact canonical policy or one direct fragment profile valid for the checked model. -/
def policySupported : CheckedAtLeastOneDateRangeOverlapsScalar model → Bool
  | .canonical source => (DateRangeFormat.ofPolicy? source.policy).isSome
  | .fragmentField source => source.profile.accepts model source.format

end CheckedAtLeastOneDateRangeOverlapsScalar

/-- A model-checked scalar-versus-list source. The shared shape spans both sides, so exact duplication or overlap between the scalar and any list operand is rejected once. -/
structure CheckedAtLeastOneDateRangeOverlapsSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  scalar : CheckedAtLeastOneDateRangeOverlapsScalar model
  first : CheckedAtLeastOneDateRangeOverlapsListOperand model
  rest : List (CheckedAtLeastOneDateRangeOverlapsListOperand model)

namespace CheckedAtLeastOneDateRangeOverlapsSource

def operands (checked : CheckedAtLeastOneDateRangeOverlapsSource model) :
    List (CheckedAtLeastOneDateRangeOverlapsListOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedAtLeastOneDateRangeOverlapsSource model) : Bool :=
  checked.operands.any CheckedAtLeastOneDateRangeOverlapsListOperand.hasHaving

end CheckedAtLeastOneDateRangeOverlapsSource

/-- Re-label one singular-operator refusal for the plural operator's side that produced it. Both sides share every operand cause, so the role is the only difference and the shared causes stay one list. -/
private def pluralOperandError (role : DateRangeOverlapSourceRole) :
    DateRangesOverlapElabError → AtLeastOneDateRangeOverlapsElabError
  | .sourceNotDateRange path actual => .sourceNotDateRange role path actual
  | .unsupportedPolicy path format separator =>
      .unsupportedPolicy role path format separator
  | .unsupportedReadForm path form => .unsupportedReadForm role path form
  | .yearInterpretationNotSupported path =>
      .yearInterpretationNotSupported role path
  | .having error => .having error
  | .shape _ | .groupsNotAllowed _ | .dateWithAndWithoutYear |
      .incoherentCore => .incoherentCore

private def certifyPluralDateRangeField (role : DateRangeOverlapSourceRole)
    (declaration : FlatFieldDecl) :
    Except AtLeastOneDateRangeOverlapsElabError
      CheckedCanonicalDateRangeField :=
  (certifyCanonicalDateRangeField declaration).mapError fun
    | .notDateRange path actual =>
        .sourceNotDateRange role path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy role path format separator
    | .incoherentCore => .incoherentCore

/-- Certify the scalar as the exact canonical policy, falling back to a direct fragment profile the model resolves. Only an unsupported canonical policy opens that fallback: any other canonical refusal, and every refusal the fragment route raises on its own, is reported as itself rather than replaced by the policy cause. -/
private def certifyPluralScalar (model : FlatModel) (declaration : FlatFieldDecl) :
    Except AtLeastOneDateRangeOverlapsElabError
      (CheckedAtLeastOneDateRangeOverlapsScalar model) :=
  match certifyPluralDateRangeField .scalar declaration with
  | .ok canonical => pure (.canonical canonical)
  | .error (.unsupportedPolicy _ _ _ _) =>
      (.fragmentField <$>
        certifyDirectDateRangeOverlapFragmentField model declaration)
        |>.mapError (pluralOperandError .scalar)
  | .error canonicalError => throw canonicalError

private def certifyAtLeastOneDateRangeOverlapScalarShape :
    ResolvedFieldEntityOperand model →
      Except AtLeastOneDateRangeOverlapsElabError
        FlatFieldDecl
  | .field declaration .stored => pure declaration
  | .field declaration form =>
      throw (.unsupportedReadForm .scalar declaration.path form)
  | .star source => throw (.scalarStarred source.declaration.path)
  | .starHaving source _ =>
      throw (.scalarFilteredStarred source.declaration.path)
  | .group reference => throw (.scalarGroup reference.path)
  | .starredGroup source => throw (.scalarGroup source.group.path)
  | .starredGroupPresence source => throw (.scalarGroup source.groupPath)

private def certifyDateRangeEntityGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except AtLeastOneDateRangeOverlapsElabError
      (CheckedDateRangeEntityGroup model) :=
  if hAll : (model.groupSubtreeFields source.groupPath).all
      (fun declaration =>
        (certifyCanonicalDateRangeField declaration).toOption.isSome) = true then
    match hOwned : (model.groupSubtreeFields source.groupPath).filterMap
        (fun declaration =>
          (certifyCanonicalDateRangeField declaration).toOption) with
    | [] => throw (.groupExpansionEmpty source.groupPath)
    | first :: rest => pure {
        source
        first
        rest
        expansionOwned := hOwned
        expansionAllDateRange := hAll }
  else
    throw (.groupExpansionNotDateRange source.groupPath)

private def certifyAtLeastOneDateRangeOverlapsListOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except AtLeastOneDateRangeOverlapsElabError
        (CheckedAtLeastOneDateRangeOverlapsListOperand model)
  | .group reference =>
      .group <$> certifyDateRangeEntityGroup model (.fixed reference)
  | .starredGroup source =>
      .group <$> certifyDateRangeEntityGroup model (.starred source)
  | .starredGroupPresence source =>
      .group <$> certifyDateRangeEntityGroup model (.starredPresence source)
  | .field declaration .stored =>
      match certifyDateRangesOverlapOperand model declaringGroup
          (.field declaration .stored) with
      | .ok canonical => pure (.field (.canonical canonical))
      | .error (.unsupportedPolicy _ _ _) =>
          ((fun fragment => .field (.fragmentField fragment)) <$>
            certifyDirectDateRangeOverlapFragmentField model declaration)
            |>.mapError (pluralOperandError .list)
      | .error canonicalError => throw (pluralOperandError .list canonicalError)
  | operand =>
      .field <$> ((.canonical <$>
        certifyDateRangesOverlapOperand model declaringGroup operand)
        |>.mapError (pluralOperandError .list))

private def certifyAtLeastOneDateRangeOverlapsListOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except AtLeastOneDateRangeOverlapsElabError
        (List (CheckedAtLeastOneDateRangeOverlapsListOperand model)) :=
  List.mapM (certifyAtLeastOneDateRangeOverlapsListOperand model declaringGroup)

/-- Resolve and gate the scalar shape before reading the list, then resolve both sides as one nonempty entity sequence so cross-side duplicate and overlap checks remain shared. Finally certify the supported DateRange policies. -/
def elaborateAtLeastOneDateRangeOverlapsSourceIn (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) :
    Except AtLeastOneDateRangeOverlapsElabError
      (CheckedAtLeastOneDateRangeOverlapsSource model) :=
  match model.validate with
  | .error error => .error (.shape (.resolve error))
  | .ok () => do
      let scalarDeclaration ←
        resolveFieldEntityOperandIn model declaringGroup scope authored.scalar
          |>.mapError .shape
          |>.bind certifyAtLeastOneDateRangeOverlapScalarShape
      let shape ← elaborateFieldEntityShapeIn model declaringGroup scope {
          first := authored.scalar
          rest := authored.list.first :: authored.list.rest
        } |>.mapError .shape
      match shape.rest with
      | [] => throw .incoherentCore
      | listFirst :: listRest => do
          match listFirst, listRest with
          | .field listed .stored, [] =>
              if scalarDeclaration.policy.kind.surfaceKind == .number &&
                  listed.policy.kind.surfaceKind == .number then
                throw (.measuredNumberPairNotDateRange
                  scalarDeclaration.path listed.path)
          | _, _ => pure ()
          if mixesDateRangeYearInclusion model (shape.first :: shape.rest) then
            throw .dateWithAndWithoutYear
          let scalar ← certifyPluralScalar model scalarDeclaration
          let first ← certifyAtLeastOneDateRangeOverlapsListOperand model
            declaringGroup listFirst
          let rest ← certifyAtLeastOneDateRangeOverlapsListOperands model
            declaringGroup listRest
          pure { shape, scalar, first, rest }

/-- The scalar instance: a source read where the reading rule iterates no level. -/
def elaborateAtLeastOneDateRangeOverlapsSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) :
    Except AtLeastOneDateRangeOverlapsElabError
      (CheckedAtLeastOneDateRangeOverlapsSource model) :=
  elaborateAtLeastOneDateRangeOverlapsSourceIn model declaringGroup [] authored

/-! ## Checked plural-overlap assembly -/

/-- The separately resolved scalar retains its checked declaration and concrete addressed cell beside the pure scalar slot. -/
structure ResolvedCheckedAtLeastOneDateRangeOverlapScalar
    (model : FlatModel) where
  private mk ::
  source : CheckedAtLeastOneDateRangeOverlapsScalar model
  core : ResolvedCheckedEntityOperandCore
  semantic : ResolvedDateRangeSlot

/-- One resolved list operand retains its authored field/group boundary and complete addressed extent beside the pure scan input. -/
structure ResolvedCheckedAtLeastOneDateRangeOverlapListOperand
    (model : FlatModel) where
  private mk ::
  source : CheckedAtLeastOneDateRangeOverlapsListOperand model
  core : ResolvedCheckedEntityOperandCore
  semantic : ResolvedDateRangeOperand

private def resolveCheckedAtLeastOneDateRangeOverlapScalar
    (source : CheckedAtLeastOneDateRangeOverlapsScalar model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedAtLeastOneDateRangeOverlapScalar model) := do
  let core ←
    (document.resolveCheckedDirectEntityOperandCoreAt outer
      source.declaration.id) |>.mapError .addressing
  match core.addressedCells with
  | [addressed] => do
      let semantic ← checkedDateRangeSlot addressed
      pure { source, core, semantic }
  | addressed => throw (.incoherentDirectOperand addressed.length)

namespace CheckedAtLeastOneDateRangeOverlapsListOperand

/-- Resolve one admitted list operand without erasing its authored field/group boundary, filter provenance, or checked group extent. -/
def resolveCheckedValidation
    (source : CheckedAtLeastOneDateRangeOverlapsListOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedAtLeastOneDateRangeOverlapListOperand model) :=
  match source with
  | .field fieldSource => do
      let core ← (fieldSource.resolveValidationCore document outer)
        |>.mapError .addressing
      let semantic ← checkedDateRangeOperandSemantic core
      pure {
        source := .field fieldSource
        core
        semantic }
  | .group groupSource => do
      let declarations :=
        (groupSource.first :: groupSource.rest).map (·.declaration)
      let core ← document.resolveCheckedGroupEntityOperandCore outer
        groupSource.source.boundLevelCount declarations
        |>.mapError .addressing
      let slots ← core.addressedCells.mapM checkedDateRangeSlot
      pure {
        source := .group groupSource
        core
        semantic := { slots, hasFilter := false } }

end CheckedAtLeastOneDateRangeOverlapsListOperand

/-- Rich resolved plural-overlap query result. The checked source keeps every authored list boundary even when an empty `operands` list records scalar-first termination; reached operands remain in authored order. -/
structure CheckedAtLeastOneDateRangeOverlapsResult (model : FlatModel) where
  private mk ::
  source : CheckedAtLeastOneDateRangeOverlapsSource model
  scalar : ResolvedCheckedAtLeastOneDateRangeOverlapScalar model
  operands : List (ResolvedCheckedAtLeastOneDateRangeOverlapListOperand model)

namespace CheckedAtLeastOneDateRangeOverlapsResult

/-- Evaluate the established scalar-versus-list scan over the resolved checked source. -/
def verdict (result : CheckedAtLeastOneDateRangeOverlapsResult model) : Verdict :=
  evalAtLeastOneDateRangeOverlaps result.scalar.semantic
    (result.operands.map (·.semantic))

end CheckedAtLeastOneDateRangeOverlapsResult

namespace CheckedAtLeastOneDateRangeOverlapsSource

private def resolveUntilFirstOverlap
    (scalar : ResolvedDateRangeSlot)
    (document : CheckedDocument model) (outer : Env) :
    List (CheckedAtLeastOneDateRangeOverlapsListOperand model) →
      Except DateRangesOverlapEvaluationError
        (List (ResolvedCheckedAtLeastOneDateRangeOverlapListOperand model))
  | [] => pure []
  | source :: remaining => do
      let resolved ← source.resolveCheckedValidation document outer
      match evalAtLeastOneDateRangeOverlaps scalar [resolved.semantic] with
      | .fired _ => pure [resolved]
      | _ => pure (resolved ::
          (← resolveUntilFirstOverlap scalar document outer remaining))

/-- Resolve the scalar first, then resolve authored list operands against the same immutable checked document only through the first overlap. -/
def evaluateCheckedDocument
    (checked : CheckedAtLeastOneDateRangeOverlapsSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (CheckedAtLeastOneDateRangeOverlapsResult model) := do
  let scalar ←
    resolveCheckedAtLeastOneDateRangeOverlapScalar checked.scalar document outer
  match scalar.semantic with
  | .skipped => pure { source := checked, scalar, operands := [] }
  | .kept _ => do
      let operands ←
        resolveUntilFirstOverlap scalar.semantic document outer checked.operands
      pure { source := checked, scalar, operands }

end CheckedAtLeastOneDateRangeOverlapsSource

end A12Kernel
