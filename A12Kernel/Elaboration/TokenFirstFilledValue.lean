import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked String/Enumeration `FirstFilledValue`

This consumer applies the common checked String/ordinary stored-Enumeration entity list to `FirstFilledValue`. It owns the operator-specific measured two-declaration kind discriminator, lazy authored-order scanning, relevance, filter selection, and token-family empty-result semantics; common token admission and declaration-owned classification stay in `TokenEntityList`.
-/

namespace A12Kernel

abbrev SurfaceFirstFilledTokenOperand := SurfaceTokenEntityOperand
abbrev SurfaceFirstFilledTokenSource := SurfaceTokenEntitySource
abbrev CheckedFirstFilledTokenField := CheckedTokenField
abbrev CheckedFirstFilledTokenStarSource := CheckedTokenStarSource
abbrev CheckedFirstFilledTokenOperand := CheckedTokenEntityOperand
abbrev CheckedFirstFilledTokenSource := CheckedTokenEntitySource

/-- Operator-specific static refusals stay outside the shared token carrier. The two measured arms
    intentionally retain only the exact two-declaration matrix established for group operands and
    their explicit expansions; every wider kind or declaration-policy combination remains an
    unmapped source refusal. -/
inductive FirstFilledTokenElabError where
  | source (error : TokenEntityElabError)
  | confirmPair (first second : List String)
  | stringNumberPair (stringPath numberPath : List String)
  deriving Repr, DecidableEq

def firstDuplicateDirectFirstFilledTokenField? :=
  @firstDuplicateDirectTokenField?

private def firstFilledMeasuredDeclarationError? :
    List FlatFieldDecl → Option FirstFilledTokenElabError
  | [first, second] =>
      match first.policy.kind.surfaceKind, second.policy.kind.surfaceKind with
      | .confirm, .confirm => some (.confirmPair first.path second.path)
      | .string, .number =>
          if first.toStoredTokenSlot?.isSome && first.customType.isNone then
            some (.stringNumberPair first.path second.path)
          else
            none
      | _, _ => none
  | _ => none

/-- Retain the exact measured carriers and declaration policies: one fixed group or two direct
    stored fields, with the String/Number arm requiring an ordinary evaluated String. Starred,
    filtered, projected, raw/custom String, reversed, and wider sources stay unmapped. -/
private def firstFilledMeasuredKindError? (model : FlatModel) :
    List (ResolvedFieldEntityOperand model) → Option FirstFilledTokenElabError
  | [.group reference] =>
      firstFilledMeasuredDeclarationError?
        (model.groupSubtreeFields reference.path)
  | [.field first .stored, .field second .stored] =>
      firstFilledMeasuredDeclarationError? [first, second]
  | _ => none

/-- Resolve the common entity-list shape first, then project only the measured `FirstFilledValue`
    kind pair before token certification would collapse both cases into a local kind mismatch. -/
def elaborateFirstFilledTokenSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFirstFilledTokenSource) :
    Except FirstFilledTokenElabError (CheckedFirstFilledTokenSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError fun error => .source (.shape error)
  match firstFilledMeasuredKindError? model shape.operands with
  | some error => throw error
  | none =>
      certifyTokenEntityShape model declaringGroup shape |>.mapError .source

namespace FirstFilledTokenElabError

/-- Project the exact measured pair and the shared shape classes. Every other token refusal remains
    unmapped rather than borrowing a diagnostic from another field-list operator. -/
def diagnostic? : FirstFilledTokenElabError → Option KernelStaticDiagnostic
  | .source (.shape error) => error.diagnostic?
  | .confirmPair _ _ => some .noBoolyAllowed
  | .stringNumberPair _ _ => some .varyingTypesNotAllowed
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
      -- This legacy raw-`Document` route cannot enumerate the group's instantiated rows. The
      -- checked-document specialization below owns the measured fixed-group fragment.
      .error (.unsupportedGroupOperand source.groupPath)
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        match state.step (source.valueListCellAt .validation directRead) with
        | .continue next => pure (.inl next)
        | .done result => pure (.inr (.evaluated result.asToken))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
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

/-- Evaluate the measured full-validation fragment in which one fixed, wholly nonrepeatable group
    is the complete `FirstFilledValue` operand list. The immutable checked document supplies the
    group's recursive field extent, each cell keeps its declaration-owned token projection, and the
    shared first-filled evaluator consumes that extent in model declaration order. `none` keeps
    every wider source outside this fragment, including a starred group, a repeatable declaration,
    or another authored operand, without confusing refusal with the evaluated `.noValue` result. -/
def evaluateCheckedFixedGroupFirstFilledValidation?
    (checked : CheckedTokenEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option FirstFilledTokenResult) :=
  match checked.first, checked.rest with
  | .group group, [] =>
      if group.isStarred ||
          !group.slots.all (fun slot => slot.declaration.repeatableScope.isEmpty) then
        pure none
      else do
        let resolved ←
          (CheckedTokenEntityOperand.group group).resolveCheckedValidationOperand
            document outer
        pure (some (evalFirstFilledToken
          (resolved.valueListSideAt .validation)))
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
