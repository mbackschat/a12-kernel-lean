import A12Kernel.Semantics.FirstFilledScan
import A12Kernel.Semantics.HavingEntityList

namespace A12Kernel.HavingFirstFilled

/-- Correlated selection uses the ordinary prefix scan while obtaining cells lazily from
candidate/captured extents. A wholly empty selection marks the prefix; an omitted tail alone
affects only exhaustion, as `FirstFilledScanState.enterSelection` requires (spec/07 §5). -/
def scanWith (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (step : FirstFilledScanState → Ref → CheckedCell → FirstFilledScanState ⊕ Result)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot Ref)) : Except Error (FirstFilledScanState ⊕ Result) :=
  HavingFieldListSlot.foldRead origin field context frame
    (fun state reference environment => do
      pure (step state reference (← context.read environment (field reference)))) {} slots
    (fun state _ => pure (.inl (state.enter true false)))
    (fun state => pure (.inl (state.enterSelection true false false)))

def number (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot HavingNumberRef)) : Except Error NumericOperand := do
  let result ← scanWith (·.origin) (·.field.id)
    (fun state _ cell => match state.step (observeCell phase cell).asNumberValueListCell with
      | .continue next => .inl next
      | .done result => .inr result) context frame slots
  pure (match result with
    | .inl state => state.finish.asValidationOperand
    | .inr result => result.asNumber.asValidationOperand)

end A12Kernel.HavingFirstFilled
