import A12Kernel.Semantics.HavingEntityList
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.ComputationFillQuantifier

namespace A12Kernel.HavingFieldFill

/-- Having validation retains the ordinary eager tally, including unknown cells and declared
omissions as separate buckets (spec/07 §5 and `ValidationFillTally`). -/
def evalValidationRead (operator : FieldFillQuantifier)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let result ← HavingFieldListSlot.foldRead (Result := Empty) (·.origin) (·.field) context frame
    (fun tally reference environment => do
      let cell ← context.read environment reference.field
      pure (.inl (tally.combine (observeCell .validation cell).asValidationFillTally)))
    { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 } slots
    (fun tally => pure (.inl { tally with uninstantiated := tally.uninstantiated + 1 }))
  match result with
  | .inl tally => pure (operator.evalValidation tally).asConservativeVerdict
  | .inr impossible => nomatch impossible

/-- Each ordinary scan program restarts the authored stream. Omitted tails occupy their
declaration's position without a cell read, preserving deciding prefixes (spec/09 §3.2). -/
def evalComputationRead (operator : FieldFillQuantifier)
    (slots : List (HavingFieldListSlot HavingPresenceRef))
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult :=
  operator.evalComputationUsing fun kind => do
    let result ← HavingFieldListSlot.foldRead (·.origin) (·.field) context frame
      (fun seen reference environment => do
        let cell ← context.read environment reference.field
        pure (FieldFillQuantifier.step kind seen (observeCell .computation cell).asComputationFillSlot))
      false slots (fun seen => pure (FieldFillQuantifier.step kind seen .uninstantiated))
    pure (match result with
      | .inl _ => .exhausted
      | .inr result => result)

end A12Kernel.HavingFieldFill
