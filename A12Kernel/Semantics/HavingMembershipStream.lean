import A12Kernel.Semantics.HavingEntityList
import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel.HavingMembershipStream

variable {Ref Error : Type} {kind : ValueListKind}

/-- Materialize each authored slot independently for validation membership (spec/06 §B.3).
Cells retain declaration-major row order; a slot's omitted declarations contribute one ORed
tail flag and no cells. These ordinary slots have no filter or nonrelevance marker. -/
def resolveSlots (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (read : Env → Ref → Except Error (ValueListCell kind))
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot Ref)) : Except Error (List (ResolvedValueListSide kind)) :=
  slots.mapM fun slot => do
    let result ← HavingFieldListSlot.foldRead (Result := Empty) origin field context frame
      (fun side reference environment => do
        let cell ← read environment reference
        pure (.inl { side with cells := cell :: side.cells }))
      (ResolvedValueListSide.empty (kind := kind)) [slot]
      (fun side _ => pure (.inl { side with hasUninstantiatedTail := true }))
    match result with
    | .inl side => pure { side with cells := side.cells.reverse }
    | .inr impossible => nomatch impossible

/-- Collect reached atoms with the reversed accumulator convention of `collectOperands`
(spec/06 §B.5). Structural faults remain outer errors; reached formal poison is an inner error.
Neither poison nor a fault acquires later rows or declarations, and omitted tails add no atom. -/
def collectSlots (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (read : Env → Ref → Except Error (ValueListCell kind))
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot Ref)) :
    Except Error (Except FormalCause (List (ValueListAtom kind))) := do
  let result ← HavingFieldListSlot.foldRead origin field context frame
    (fun values reference environment => do
      let cell ← read environment reference
      pure (match ValueListCell.scanPresent (fun acc value => value :: acc) [cell] values with
        | .ok next => .inl next
        | .error cause => .inr (.error cause))) [] slots
  pure (match result with
    | .inl values => .ok values
    | .inr result => result)

/-- Search only the computation prefix reached before a match or formal poison (spec/06 §B.5).
Structural faults remain outer errors; an exhausted stream returns inner `ok false`.
Omitted tails contribute neither a match nor poison. -/
def anySlots (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (read : Env → Ref → Except Error (ValueListCell kind))
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot Ref)) (predicate : ValueListAtom kind → Bool) :
    Except Error (Except FormalCause Bool) := do
  let result ← HavingFieldListSlot.foldRead origin field context frame
    (fun _ reference environment => do
      let cell ← read environment reference
      pure (match ValueListCell.anyComputation predicate [cell] with
        | .ok false => .inl ()
        | outcome => .inr outcome)) () slots
  pure (match result with
    | .inl _ => .ok false
    | .inr result => result)

end A12Kernel.HavingMembershipStream
