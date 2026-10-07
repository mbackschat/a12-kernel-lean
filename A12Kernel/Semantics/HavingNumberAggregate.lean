import A12Kernel.Semantics.HavingEntityList
import A12Kernel.Semantics.NumericAggregate

namespace A12Kernel.HavingNumberAggregate

def presenceSlots (slots : List (HavingFieldListSlot HavingNumberRef)) :
    List (HavingFieldListSlot HavingPresenceRef) :=
  slots.map (·.map fun reference => { origin := reference.origin, field := reference.field.id })

/-- The ordinary aggregate fold consumes declaration-major cells and retains each omitted
declaration's signedness for directional validation (spec/04 aggregates, spec/07 §5).
The first unavailable cell stops acquisition in both phases, as in `scanResolvedValueListOperands`.
An unfiltered operand inside Having does not itself acquire a filter marker. -/
def evaluate (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (op : NumericAggregateOp) (slots : List (HavingFieldListSlot HavingNumberRef)) :
    Except Error NumericOperand := do
  let result ← HavingFieldListSlot.foldRead (·.origin) (·.field.id) context frame
    (fun accumulated reference environment => do
      let cell ← context.read environment reference.field.id
      match (observeCell phase cell).asNumberValueListCell with
      | .unknown cause => pure (.inr (NumericOperand.unknown cause))
      | value => pure (.inl (accumulated.append reference.field.info.signed {
          cells := [value], hasUninstantiatedTail := false, hasHaving := false })))
    ({} : ResolvedNumberEntityAggregateSides) slots
    (fun accumulated reference => pure (.inl (accumulated.append reference.field.info.signed {
      cells := [], hasUninstantiatedTail := true, hasHaving := false })))
  pure (match result with
    | .inl accumulated => accumulated.evaluate op
    | .inr unavailable => unavailable)

end A12Kernel.HavingNumberAggregate
