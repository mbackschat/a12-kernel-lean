import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked String/Enumeration distinct counts

This consumer applies the common checked String/ordinary stored-Enumeration entity list to `NumberOfDifferentValues`. It owns all-rows partial relevance, aggregate filter skipping, integral result scale, and the distinct-count fold; token admission and classification stay in `TokenEntityList`.
-/

namespace A12Kernel

abbrev SurfaceTokenDistinctCountOperand := SurfaceTokenEntityOperand
abbrev SurfaceTokenDistinctCountSource := SurfaceTokenEntitySource
abbrev CheckedTokenDistinctField := CheckedTokenField
abbrev CheckedTokenDistinctStarSource := CheckedTokenStarSource
abbrev CheckedTokenDistinctOperand := CheckedTokenEntityOperand
abbrev CheckedTokenDistinctSource := CheckedTokenEntitySource
/-- This operator's own refusals beside the shared token list's.

    The two extra arms exist because the Kernel's classes here are **positional** and the shared
    error is not: `TokenEntityElabError.fieldKindMismatch` carries the offending operand's path but
    not the list's first operand, so a Number in first position and a Number in third produce
    indistinguishable values while drawing different Kernel codes. The authored shape still has the
    order, which is why these are detected before certification rather than projected after it. -/
inductive TokenDistinctCountElabError where
  | source (error : TokenEntityElabError)
  /-- A **later** operand outside the string family in a string-family-first list. The Kernel reports
      homogeneity from the first operand's family, so this is the string-family half of the pair
      whose Number-first half draws `MVK_NUMBER_AND_NON_NUMBER` at the Number consumer. -/
  | laterNonToken (path : List String) (actual : SurfaceScalarKind)
  /-- An operand outside the operator's kind domain — string, enumeration, number, and date/time —
      from **any** position, because the domain is checked before homogeneity is. -/
  | kindOutsideDomain (path : List String) (actual : SurfaceScalarKind)
  deriving Repr, DecidableEq

def firstDuplicateDirectTokenDistinctField? :=
  @firstDuplicateDirectTokenField?

/-- Whether this kind belongs to the string family for **this** operator. A Custom-declared field is
    an ordinary `.string` kind here and is admitted with the family, which is the opposite of the
    custom-type validity predicate's answer for the same declaration; one field kind, two operators,
    two answers ([checkpoint](../../docs/SOURCES.md#src-distinct-count-operand-domain)). -/
private def isTokenFamilyKind : SurfaceScalarKind → Bool
  | .string | .enumeration => true
  | _ => false

/-- Whether this kind is outside the operator's admitted domain altogether. -/
private def isOutsideDistinctDomain : SurfaceScalarKind → Bool
  | .boolean | .confirm => true
  | _ => false

/-- The declaration one resolved slot reads directly, or `none` for a slot whose kind this
    positional pre-check does not resolve. A group or starred-group slot expands to many
    declarations with no single kind, and no row measures the positional class through one, so those
    stay unclassified here and reach the shared certification unchanged. -/
private def directSlotDeclaration? :
    ResolvedFieldEntityOperand model → Option FlatFieldDecl
  | .field declaration _ => some declaration
  | .star source | .starHaving source _ => some source.declaration
  | .group _ | .starredGroup _ | .starredGroupPresence _ => none

/-- Project this operator's positional classes from the authored order, before token certification
    collapses every kind failure into one unpositioned mismatch.

    The domain test runs over **every** slot and the homogeneity test only over later ones, which is
    the order the Kernel applies them in: a Boolean draws the domain code wherever it sits, while a
    Number draws a homogeneity code that depends on what preceded it. A first operand that is
    neither token-family nor outside the domain — a Number — means the list was never this
    overload's, so nothing is classed and the Number consumer owns it. -/
private def distinctPositionalError? (operands : List (ResolvedFieldEntityOperand model)) :
    Option TokenDistinctCountElabError :=
  let kinds := operands.filterMap fun operand =>
    (directSlotDeclaration? operand).map fun declaration =>
      (declaration.path, declaration.policy.kind.surfaceKind)
  match kinds.find? (fun entry => isOutsideDistinctDomain entry.2) with
  | some (path, actual) => some (.kindOutsideDomain path actual)
  | none =>
      match kinds with
      | (_, firstKind) :: later =>
          if isTokenFamilyKind firstKind then
            (later.find? (fun entry => !isTokenFamilyKind entry.2)).map
              fun (path, actual) => .laterNonToken path actual
          else none
      | [] => none

/-- Resolve the shared shape, class this operator's positional refusals from the authored order, and
    otherwise certify through the common token list unchanged. -/
def elaborateTokenDistinctCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenDistinctCountSource) :
    Except TokenDistinctCountElabError (CheckedTokenEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError fun error => .source (.shape error)
  match distinctPositionalError? shape.operands with
  | some error => throw error
  | none =>
      certifyTokenEntityShape model declaringGroup shape |>.mapError .source

namespace TokenDistinctCountElabError

/-- Project this operator's two positional classes and delegate every shared shape refusal. A token
    refusal that is not one of the two stays unmapped rather than borrowing a sibling's class. -/
def diagnostic? : TokenDistinctCountElabError → Option KernelStaticDiagnostic
  | .source (.shape error) => error.diagnostic?
  | .laterNonToken _ _ => some .stringEnumAndNonStringEnum
  | .kindOutsideDomain _ _ => some .onlyStringEnumNumberCmpDateAllowed
  | .source _ => none

end TokenDistinctCountElabError

namespace CheckedTokenEntitySource

/-- `NumberOfDifferentValues` always has integral scale 0 and no literal-driven scale expansion. -/
def distinctScaleSummary (_checked : CheckedTokenEntitySource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

end CheckedTokenEntitySource

namespace CheckedTokenEntitySource

/-- Evaluate full validation in authored slot order. Every wildcard occurrence resolves independently, and the first unavailable reached cell stops before later topology or reads. -/
def evaluateDistinctValidation (checked : CheckedTokenEntitySource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide .token) (terminal := NumericOperand)
      (fun operand => do
        pure (.inl (← operand.resolvedValidationSide document outer
          directRead starRead)))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.append side)
      checked.operands ResolvedValueListSide.empty with
  | .inl side => pure (evalDistinctCountAggregate side)
  | .inr result => pure result

/-- Evaluate full validation from the immutable checked document through the shared rich addressed operand construction. Consumer-specific first-unavailability stopping and distinct-token folding remain here. -/
def evaluateCheckedDocumentDistinctValidation
    (checked : CheckedTokenEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide .token) (terminal := NumericOperand)
      (fun operand => do
        let resolved ←
          operand.resolveCheckedValidationOperand document outer
        pure (.inl (resolved.inCapacityValueListSideAt .validation)))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.append side)
      checked.operands ResolvedValueListSide.empty with
  | .inl side => pure (evalDistinctCountAggregate side)
  | .inr result => pure result

/-- Partial validation skips a filtered rule before topology or reads. Otherwise direct slots require concrete relevance and every star requires wildcard/ancestor all-rows coverage. -/
def evaluatePartialDistinctValidation (checked : CheckedTokenEntitySource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError PartialValidationAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedValueListSide .token)
        (terminal := PartialValidationAggregateResult)
        (fun operand => operand.resolvedPartialValidationSide document outer scope
          directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.append side)
        checked.operands ResolvedValueListSide.empty with
    | .inl side => pure (.evaluated (evalDistinctCountAggregate side))
    | .inr result => pure result

end CheckedTokenEntitySource

end A12Kernel
