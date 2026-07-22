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
abbrev TokenDistinctCountElabError := TokenEntityElabError

def firstDuplicateDirectTokenDistinctField? :=
  @firstDuplicateDirectTokenField?

def elaborateTokenDistinctCountSource := elaborateTokenEntitySource

namespace CheckedTokenEntitySource

/-- `NumberOfDifferentValues` always has integral scale 0 and no literal-driven scale expansion. -/
def distinctScaleSummary (_checked : CheckedTokenEntitySource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

end CheckedTokenEntitySource

namespace CheckedTokenStarSource

/-- Full validation resolves topology and its optional checked filter before classifying selected target cells. -/
def resolvedDistinctValidationSide (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide document outer
    checked.filter read (checked.valueListCellAt .validation read)

/-- Partial all-rows validation checks wildcard/ancestor extent before reading any selected target. -/
def resolvedPartialDistinctValidationSide
    (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) Unit) := do
  let resolved ← checked.source.path.resolve document outer
  if checked.source.allRowsRelevant scope then
    pure (.inl (resolved.toResolvedSide
      (checked.valueListCellAt .validation read)))
  else
    pure (.inr ())

end CheckedTokenStarSource

namespace CheckedTokenEntityOperand

def resolvedDistinctValidationSide (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .field source => pure (source.resolvedSideAt .validation directRead)
  | .star source =>
      source.resolvedDistinctValidationSide document outer starRead

def resolvedPartialDistinctValidationSide
    (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) PartialValidationAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedSideAt .validation directRead))
      else
        pure (.inr .nonRelevant)
  | .star source =>
      if hUnfiltered : source.filter.isNone = true then do
        match ← source.resolvedPartialDistinctValidationSide document outer scope
            starRead hUnfiltered with
        | .inl side => pure (.inl side)
        | .inr () => pure (.inr .nonRelevant)
      else
        pure (.inr .skippedHaving)

end CheckedTokenEntityOperand

namespace CheckedTokenEntitySource

private def emptySide : ResolvedValueListSide .token :=
  { cells := [], hasUninstantiatedTail := false, hasHaving := false }

/-- Evaluate full validation in authored slot order. Every wildcard occurrence resolves independently, and the first unavailable reached cell stops before later topology or reads. -/
def evaluateDistinctValidation (checked : CheckedTokenEntitySource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide .token) (terminal := NumericOperand)
      (fun operand => do
        pure (.inl (← operand.resolvedDistinctValidationSide document outer
          directRead starRead)))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.append side)
      checked.operands emptySide with
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
        (fun operand => operand.resolvedPartialDistinctValidationSide document outer scope
          directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.append side)
        checked.operands emptySide with
    | .inl side => pure (.evaluated (evalDistinctCountAggregate side))
    | .inr result => pure result

end CheckedTokenEntitySource

end A12Kernel
