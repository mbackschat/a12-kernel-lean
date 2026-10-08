import A12Kernel.Semantics.TemporalDistinctCount
import A12Kernel.Semantics.ValueCountInputs
import A12Kernel.Semantics.HavingEntityList
import A12Kernel.Semantics.FieldFillQuantifier
import A12Kernel.Semantics.ComputationFillQuantifier

namespace A12Kernel

/-- Count sources retain authored extents and declared capacity separately: current rows do
not determine validation movement (spec/07 §5, spec/09 §3.2). -/
inductive HavingCollectionCount where
  | filledFields (slots : List (HavingFieldListSlot HavingPresenceRef)) (capacity : Option Nat)
  | numberValue (expected : Rat) (slots : List (HavingFieldListSlot HavingNumberRef))
  | tokenValue (expected : String) (slots : List (HavingFieldListSlot HavingStringRef))
  | temporalDistinct (baseYear : Option Int) (components : TemporalComponents)
      (slots : List (HavingFieldListSlot HavingTemporalRef))
  | tokenDistinct (slots : List (HavingFieldListSlot HavingStringRef))
  | booleanValue (expected : Bool) (slots : List (HavingFieldListSlot HavingPresenceRef))
  deriving Repr, DecidableEq

namespace HavingCollectionCount

def presenceSlots : HavingCollectionCount → List (HavingFieldListSlot HavingPresenceRef)
  | .filledFields slots _ | .booleanValue _ slots => slots
  | .tokenValue _ slots | .tokenDistinct slots => slots.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })
  | .temporalDistinct _ _ slots => slots.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })
  | .numberValue _ slots => slots.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })

/-- An unfiltered list within a filter is still unfiltered for count movement. Acquisition
stops at its first unavailable value, as in `evalResolvedValueCountOperands` (spec/04). -/
def evaluateTypedCount (finish : ResolvedValueListSide kind → NumericOperand)
    (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (read : Ref → CheckedCell → ValueListCell kind)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot Ref)) : Except Error NumericOperand := do
  let result ← HavingFieldListSlot.foldRead origin field context frame
    (fun accumulated reference environment => do
      match read reference (← context.read environment (field reference)) with
      | .unknown cause => pure (.inr (NumericOperand.unknown cause))
      | value => pure (.inl { accumulated with cells := value :: accumulated.cells }))
    ({ cells := [], hasUninstantiatedTail := false, hasHaving := false } : ResolvedValueListSide kind) slots
    (fun accumulated _ => pure (.inl { accumulated with hasUninstantiatedTail := true }))
  pure (match result with
    | .inl accumulated => finish { accumulated with cells := accumulated.cells.reverse }
    | .inr unavailable => unavailable)

def evaluateValueCount (expected : ValueListAtom kind)
    (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (read : Ref → CheckedCell → ValueListCell kind)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot Ref)) : Except Error NumericOperand :=
  evaluateTypedCount (fun side => evalValueCountAggregate expected (ResolvedValueCountSide.empty.appendResolved side))
    origin field read context frame slots

/-- The kernel count stops on its first unavailable cell, before acquiring any later field or
extent (`RuntimeController.anzahlAngegebenerEntities`, kernel 30.8.1). Capacity remains a
separate static input; an omitted row contributes no filled cell. -/
def evaluate (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : HavingCollectionCount → Except Error (Option NumericOperand)
  | .numberValue expected slots =>
      some <$> evaluateValueCount expected (·.origin) (·.field.id)
        (fun ref cell => ref.field.valueListCellAt phase { read := fun _ => cell }) context frame slots
  | .tokenValue expected slots =>
      some <$> evaluateValueCount expected (·.origin) (·.field.id)
        (fun ref cell => ref.operand.checkedValueListCellAt phase cell) context frame slots
  | .temporalDistinct baseYear components slots =>
      let arm := temporalDistinctCountFoldArm components baseYear.isSome
      some <$> evaluateTypedCount (kind := arm.kind) evalDistinctCountAggregate (·.origin) (·.field.id)
        (fun ref cell => temporalDistinctCountCell phase ref.field.components baseYear arm cell) context frame slots
  | .tokenDistinct slots =>
      some <$> evaluateTypedCount evalDistinctCountAggregate (·.origin) (·.field.id)
        (fun ref cell => ref.operand.checkedValueListCellAt phase cell) context frame slots
  | .booleanValue expected slots =>
      some <$> evaluateValueCount (booleanValueCountToken expected) (·.origin) (·.field)
        (fun _ cell => booleanValueCountCellAt phase cell) context frame slots
  | .filledFields slots capacity => do
      let result ← HavingFieldListSlot.foldRead (·.origin) (·.field) context frame
        (fun total ref environment => do
          let cell ← context.read environment ref.field
          match numberOfFilledFieldsForComputation [(observeCell phase cell).asComputationFillSlot] with
          | .error cause => pure (.inr cause)
          | .ok count => pure (.inl (total + count))) 0 slots
      pure (match result with
        | .inr cause => some (.unknown cause)
        | .inl total => match phase with
            | .computation => some (.value total .fixed)
            | .validation => capacity.bind fun bound =>
                ((FilledFieldCount.value total).availableWithFillability? bound).map fun (count, movement) =>
                  .value count movement)

end HavingCollectionCount
end A12Kernel
