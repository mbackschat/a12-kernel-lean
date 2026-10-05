import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked String/Enumeration `FirstFilledValue`

This consumer applies the common checked String/ordinary stored-Enumeration entity list to `FirstFilledValue`. It owns the operator-specific Confirm and type classes over the expanded list, lazy authored-order scanning, relevance, filter selection, and token-family empty-result semantics; common token admission and declaration-owned classification stay in `TokenEntityList`.
-/

namespace A12Kernel

abbrev SurfaceFirstFilledTokenOperand := SurfaceTokenEntityOperand
abbrev SurfaceFirstFilledTokenSource := SurfaceTokenEntitySource
abbrev CheckedFirstFilledTokenField := CheckedTokenField
abbrev CheckedFirstFilledTokenStarSource := CheckedTokenStarSource
abbrev CheckedFirstFilledTokenOperand := CheckedTokenEntityOperand
abbrev CheckedFirstFilledTokenSource := CheckedTokenEntitySource

/-- Operator-specific static refusals stay outside the shared token carrier. Both kind arms are read
    off the expanded list and projected only where a row measures them; every other kind or
    declaration-policy combination remains an unmapped source refusal. -/
inductive FirstFilledTokenElabError where
  | source (error : TokenEntityElabError)
  /-- The first Confirm declaration of the expanded list. -/
  | confirmOperand (path : List String)
  /-- The expanded list's first declaration and the first later one of another type family. -/
  | varyingTypes (leaderPath memberPath : List String)
  deriving Repr, DecidableEq

def firstDuplicateDirectFirstFilledTokenField? :=
  @firstDuplicateDirectTokenField?

/-- The type families this classifier compares. Raw String, temporal, and DateRange declarations
    have none here, so a list holding one stays unmapped: the temporal and DateRange rows key the
    family on the declared format, and no row places a raw String at this gate. -/
private inductive FirstFilledTypeFamily where
  | text
  | boolean
  | number
  deriving DecidableEq

private def firstFilledTypeFamily? (declaration : FlatFieldDecl) :
    Option FirstFilledTypeFamily :=
  match declaration.policy.kind.surfaceKind with
  | .string => if declaration.isRawString then none else some .text
  | .enumeration => some .text
  | .boolean => some .boolean
  | .number => some .number
  | .confirm | .temporal _ | .dateRange => none

/-- Whether a leader/member split is measured to draw the type class. Only the measured order counts:
    every text/Number and Boolean/Number row leads with the text or the Boolean, and the text/Boolean
    rows lead with an ordinary String, so neither a reversed pair nor a Custom or Enumeration leader
    beside a Boolean borrows the class. -/
private def measuredTypeSplit (leader member : FlatFieldDecl) : Bool :=
  match leader.policy.kind.surfaceKind, member.policy.kind.surfaceKind with
  | .string, .number | .enumeration, .number | .boolean, .number => true
  | .string, .boolean => leader.customType.isNone
  | _, _ => false

/-- The declarations a list contributes to the kind gates when every operand is a carrier those
    gates are measured on: a direct stored field, or a fixed group read through its recursive
    expansion. Starred, filtered, and projected operands leave the whole list unclassified. -/
private def measuredKindExpansion? (model : FlatModel) :
    List (ResolvedFieldEntityOperand model) → Option (List FlatFieldDecl)
  | [] => some []
  | .field declaration .stored :: rest =>
      (declaration :: ·) <$> measuredKindExpansion? model rest
  | .group reference :: rest =>
      (model.groupSubtreeFields reference.path ++ ·) <$> measuredKindExpansion? model rest
  | _ :: _ => none

/-- The Confirm class is asked over the whole expanded list before the type class, so a Confirm
    declaration in any position decides the list
    ([inbound](../../docs/SOURCES.md#inbound-2026-09-23-first-filled-gate-positions)). The type
    class compares each later declaration with the first and is projected only for a measured split
    between the leader and the first member of another family. -/
private def firstFilledMeasuredKindError? (model : FlatModel)
    (operands : List (ResolvedFieldEntityOperand model)) :
    Option FirstFilledTokenElabError := do
  let declarations ← measuredKindExpansion? model operands
  match declarations.find? (·.policy.kind.surfaceKind == .confirm) with
  | some confirm => pure (.confirmOperand confirm.path)
  | none =>
      let leader :: members := declarations | none
      let leaderFamily ← firstFilledTypeFamily? leader
      let families ← members.mapM firstFilledTypeFamily?
      let (member, _) ← (members.zip families).find? (·.2 != leaderFamily)
      if measuredTypeSplit leader member then
        pure (.varyingTypes leader.path member.path)
      else
        none

/-- Resolve the common entity-list shape first, then project the measured `FirstFilledValue` kind
    classes before token certification would collapse them into a local kind mismatch. -/
def elaborateFirstFilledTokenSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFirstFilledTokenSource)
    (writtenGroup : GroupPath := declaringGroup) (bindingGroup? : Option GroupPath := none) :
    Except FirstFilledTokenElabError (CheckedFirstFilledTokenSource model) := do
  let shape ← elaborateFieldEntityShapeIn model declaringGroup
    (bindingGroup?.map model.repeatableScopeForGroupPath |>.getD []) authored
    (writtenGroup := writtenGroup)
    |>.mapError fun error => .source (.shape error)
  match firstFilledMeasuredKindError? model shape.operands with
  | some error => throw error
  | none =>
      certifyTokenEntityShape model declaringGroup shape (bindingGroup?.getD declaringGroup) |>.mapError .source

namespace FirstFilledTokenElabError

/-- Project the measured kind classes and the shared shape classes. Every other token refusal remains
    unmapped rather than borrowing a diagnostic from another field-list operator. -/
def diagnostic? : FirstFilledTokenElabError → Option KernelStaticDiagnostic
  | .source (.shape error) => error.diagnostic?
  | .confirmOperand _ => some .noBoolyAllowed
  | .varyingTypes _ _ => some .varyingTypesNotAllowed
  -- The filter's class is the **filter's own**, measured identical across three structurally
  -- different wrapping carriers ([checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes)),
  -- so it delegates here rather than being dropped. Only the filter half delegates: the shared
  -- token checker's **kind** classes were measured against a String-literal value list and this is
  -- a different operator with its own message vocabulary.
  | .source (.having error) => error.diagnostic?
  | .source _ => none

end FirstFilledTokenElabError

/-- Partial validation keeps a reached nonrelevant token cell distinct from formal unavailability, exhaustion, and a selected token. -/
inductive PartialValidationFirstFilledTokenResult where
  | nonRelevant
  | evaluated (result : FirstFilledTokenResult)
  deriving Repr, DecidableEq

namespace CheckedTokenStarSource

/-- Continue one reached star slot in encounter order. Relevance is checked immediately before declaration-owned target classification. -/
def scanPartialFirstFilledState (checked : CheckedTokenStarSource model)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell) :
    List Env → FirstFilledScanState →
      FirstFilledScanState ⊕ PartialValidationFirstFilledTokenResult
  | [], state => .inl state
  | environment :: environments, state =>
      if checked.source.cellRelevant scope environment then
        match state.step (checked.valueListCellAt .validation read environment) with
        | .continue next =>
            checked.scanPartialFirstFilledState scope read environments next
        | .done result => .inr (.evaluated result.asToken)
      else
        .inr .nonRelevant

end CheckedTokenStarSource

private def scanCheckedFirstFilledTokenOperand
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell)
    (state : FirstFilledScanState) :
    CheckedTokenEntityOperand model →
      Except StarAddressingError
        (FirstFilledScanState ⊕ PartialValidationFirstFilledTokenResult)
  | .group source =>
      -- No observation measures a token group on this raw-`Document` route
      -- ([SG5](../../docs/gaps/numeric-and-temporal.md#gap-sg5-number-token-group-runtime)), so it
      -- refuses; the checked-document specialization below owns the measured fixed-group fragment.
      .error (.unsupportedGroupOperand source.groupPath)
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        match state.step (source.valueListCellAt .validation directRead) with
        | .continue next => pure (.inl next)
        | .done result => pure (.inr (.evaluated result.asToken))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolveInCapacity document outer
      let selected := match source.filter with
        | none => resolved.environments
        | some filter =>
            filter.condition.selectEnvironments { read := starRead } outer
              resolved.environments
      pure (source.scanPartialFirstFilledState scope starRead selected
        (state.enterSelection selected.isEmpty resolved.domain.hasOpenTail
          source.filter.isSome))

private def scanCheckedFirstFilledTokenOperands
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    List (CheckedTokenEntityOperand model) → FirstFilledScanState →
      Except StarAddressingError PartialValidationFirstFilledTokenResult
  | [], _ => pure (.evaluated .noValue)
  | operand :: remaining, state => do
      match ← scanCheckedFirstFilledTokenOperand document outer scope directRead
          starRead state operand with
      | .inl next =>
          scanCheckedFirstFilledTokenOperands document outer scope directRead starRead
            remaining next
      | .inr result => pure result

namespace CheckedTokenEntitySource

private inductive GroupFirstFilledRuntimeShape where
  | fixed
  | directSingleStar

/-- A fixed source binds every repeatable level above its authored terminal and may therefore walk
    repeatable descendants, but a terminal that is itself repeatable belongs to the separate
    iteration-owned account. The starred specialization stays on its measured direct one-level shape. -/
private def groupFirstFilledRuntimeShape?
    (group : CheckedTokenEntityGroup model) : Option GroupFirstFilledRuntimeShape :=
  match group.source with
  | .fixed _ =>
      if !model.repeatableGroups.any (fun repeatable =>
          repeatable.path == group.groupPath) then
        some .fixed
      else
        none
  | .starred _ =>
      let scope := model.repeatableScopeForGroupPath group.groupPath
      if scope.length == 1 && group.slots.all (fun slot =>
          slot.declaration.groupPath == group.groupPath &&
            slot.declaration.repeatableScope == scope) then
        some .directSingleStar
      else
        none
  | .starredPresence _ => none

private def resolveCheckedFirstFilledValidationSide
    (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (ResolvedValueListSide .token) := do
  match source with
  | .field direct => do
      let addressed ← document.fullValidationAddressedCell outer direct.declaration.id
      pure { cells := [direct.operand.checkedValueListCellAt .validation addressed.cell]
             hasUninstantiatedTail := false, hasHaving := false }
  | .star _ | .group _ => do
      pure ((← source.resolveCheckedValidationOperand document outer)
        |>.inCapacityValueListSideAt .validation)

/-- Stored-token sources share the same scan across direct, starred and group operands.
    Group certificates already require stored projections; explicit category projections remain
    outside this route. -/
def supportsCheckedFirstFilledValidation
    (checked : CheckedTokenEntitySource model) : Bool :=
  checked.operands.all fun
    | .group _ => true
    | .field source => source.projectionRef == .stored
    | .star source => source.projectionRef == .stored

private def scanCheckedFirstFilledValidationOperands
    (document : CheckedDocument model) (outer : Env) :
    List (CheckedTokenEntityOperand model) → FirstFilledScanState →
      Except CheckedAddressingError FirstFilledTokenResult
  | [], _ => pure .noValue
  | operand :: remaining, state => do
      let side ← resolveCheckedFirstFilledValidationSide operand document outer
      match scanFirstFilledItems id side.cells (state.enterOperand side) with
      | .inl next =>
          scanCheckedFirstFilledValidationOperands document outer remaining next
      | .inr result => pure result.asToken

/-- Evaluate a supported stored-token source. The support proof excludes projected slots before
traversal, so condition consumers need no fallback that could disguise an unsupported shape. -/
def evaluateSupportedFirstFilledValidation
    (checked : CheckedTokenEntitySource model) (document : CheckedDocument model) (outer : Env)
    (_supported : checked.supportsCheckedFirstFilledValidation = true) :
    Except CheckedAddressingError FirstFilledTokenResult :=
  scanCheckedFirstFilledValidationOperands document outer checked.operands {}

/-- Evaluate one already-admitted direct/plain-star/filtered-star/group token source against the immutable
    checked document. A bound direct slot retains its formal findings; reopened star/group slots select their
    in-capacity projection before the common lazy scan; a terminal value or formal cause hides every later slot and its addressing work.
    `none` denotes a projected source outside this stored-token account. -/
def evaluateCheckedFirstFilledValidation?
    (checked : CheckedTokenEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option FirstFilledTokenResult) :=
  if supported : checked.supportsCheckedFirstFilledValidation = true then do
    pure (some (← checked.evaluateSupportedFirstFilledValidation document outer supported))
  else
    pure none

/-- Evaluate the measured full-validation group fragments through the immutable checked document.
    One fixed group whose authored terminal is nonrepeatable, including its recursive repeatable
    descendants, and one direct single-level group star are complete operand lists; the measured
    group-star form may additionally precede one nonrepeatable direct fallback.
    Every reached cell keeps its declaration-owned token projection, and the shared first-filled
    evaluator consumes resolved operands in authored order and group cells declaration-major.
    `none` keeps every wider source outside without confusing refusal with `.noValue`. -/
def evaluateCheckedGroupFirstFilledValidation?
    (checked : CheckedTokenEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option FirstFilledTokenResult) :=
  match checked.first, checked.rest with
  | .group group, [] =>
      match groupFirstFilledRuntimeShape? group with
      | none => pure none
      | some _ => do
          let side ←
            resolveCheckedFirstFilledValidationSide
              (.group group) document outer
          pure (some (evalFirstFilledToken side))
  | .group group, [.field fallback] =>
      match groupFirstFilledRuntimeShape? group with
      | some .directSingleStar => do
          let first ←
            resolveCheckedFirstFilledValidationSide
              (.group group) document outer
          let second ←
            resolveCheckedFirstFilledValidationSide
              (.field fallback) document outer
          pure (some (evalFirstFilledTokenOperands { first, rest := [second] }))
      | some .fixed | none => pure none
  | _, _ => pure none

/-- Evaluate checked direct and independently resolved star slots in authored order. Later topology, filters, relevance, and target reads remain unobserved after a terminal prefix. -/
def evaluatePartialFirstFilledValidation
    (checked : CheckedTokenEntitySource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationFirstFilledTokenResult :=
  scanCheckedFirstFilledTokenOperands document outer scope directRead starRead
    checked.operands {}

end CheckedTokenEntitySource

end A12Kernel
