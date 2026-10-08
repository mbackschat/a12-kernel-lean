import A12Kernel.Semantics.DateRangeOverlapOperators
import A12Kernel.Semantics.Correlation

namespace A12Kernel

namespace ComputationOverlapSearch

/-- Consume an unfiltered stream without forcing the suffix after a decision. The reader
also passes `step` to the existing filtered iterator, which owns its lookahead order. -/
def scan (overlaps : α → α → Bool) (read : slot → Except error (CellObservation α)) :
    List slot → ComputationOverlapSearch α →
      Except error (ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult)
  | [], state => pure (.exhausted state)
  | slot :: rest, state => do
      match state.step overlaps (← read slot) with
      | .inl next => scan overlaps read rest next
      | .inr result => pure (.terminated result)

def result : ComputationHavingScanResult (ComputationOverlapSearch α) ComputationConditionResult →
    ComputationConditionResult
  | .exhausted _ => .notTrue
  | .terminated outcome => outcome
  | .poison cause => .poison cause


end ComputationOverlapSearch
end A12Kernel
