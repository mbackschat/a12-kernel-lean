import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.Correlation

namespace A12Kernel

/-- The plural operator keeps its scalar fixed; the any-pair operator accumulates earlier
ranges. This distinction prevents list-internal matches from deciding a scalar-versus-list guard. -/
inductive ComputationOverlapSearch (α : Type) where
  | anyPair (seen : List α)
  | against (scalar : α)
  deriving Repr, DecidableEq

namespace ComputationOverlapSearch

/-- A reached invalid cell aborts computation, while an empty cell leaves the search unchanged.
The overlap-guard kernel grid (2026-10-04) separates both effects from an unread invalid suffix. -/
def step (overlaps : α → α → Bool) (search : ComputationOverlapSearch α) :
    CellObservation α → ComputationOverlapSearch α ⊕ ComputationConditionResult
  | .empty => .inl search
  | .unknown cause | .poison cause => .inr (.poison cause)
  | .value value => match search with
      | .anyPair seen => if seen.any (overlaps value) then .inr .holds
          else .inl (.anyPair (value :: seen))
      | .against scalar => if overlaps scalar value then .inr .holds else .inl search

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

/-- An empty scalar bypasses the entire list, including its filter and addressing effects. -/
def scalarUsing (scalar : CellObservation α)
    (scanList : ComputationOverlapSearch α → Except error ComputationConditionResult) :
    Except error ComputationConditionResult :=
  match scalar with
  | .empty => pure .notTrue
  | .unknown cause | .poison cause => pure (.poison cause)
  | .value value => scanList (.against value)

end ComputationOverlapSearch
end A12Kernel
