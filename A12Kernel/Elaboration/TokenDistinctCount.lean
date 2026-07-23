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
        pure (.inl (← operand.resolvedValidationSide document outer
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
        (fun operand => operand.resolvedPartialValidationSide document outer scope
          directRead starRead)
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.append side)
        checked.operands emptySide with
    | .inl side => pure (.evaluated (evalDistinctCountAggregate side))
    | .inr result => pure result

end CheckedTokenEntitySource

end A12Kernel
