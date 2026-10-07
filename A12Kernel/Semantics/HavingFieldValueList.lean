import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.HavingMembershipStream
import A12Kernel.Semantics.HavingGroupPresence

namespace A12Kernel

def HavingNumberRef.readValueListCell (ref : HavingNumberRef) (phase : Phase)
    (read : HavingOrigin → FieldId → Except Error CheckedCell) : Except Error (ValueListCell .number) := do
  let cell ← read ref.origin ref.field.id
  pure (ref.field.valueListCellAt phase { read := fun _ => cell })

def HavingStringRef.readValueListCell (ref : HavingStringRef) (phase : Phase)
    (read : HavingOrigin → FieldId → Except Error CheckedCell) : Except Error (ValueListCell .token) := do
  pure (ref.operand.checkedValueListCellAt phase (← read ref.origin ref.field.id))

/-- Membership over authored field-list slots retains each operand's origin and checked value domain.
Category identity remains in the token operand, independently of its physical field ID (spec/06 §B.4). -/
inductive HavingFieldValueList where
  | number (subjects members : List (HavingFieldListSlot HavingNumberRef))
  | token (subjects members : List (HavingFieldListSlot HavingStringRef))
  | tokenLiterals (subjects : List (HavingFieldListSlot HavingStringRef)) (members : List String)
  deriving Repr, DecidableEq

namespace HavingFieldValueList

def presenceSlots : HavingFieldValueList → List (HavingFieldListSlot HavingPresenceRef)
  | .number subjects members => (subjects ++ members).map (·.map fun ref => { origin := ref.origin, field := ref.field.id })
  | .token subjects members => (subjects ++ members).map (·.map fun ref => { origin := ref.origin, field := ref.field.id })
  | .tokenLiterals subjects _ => subjects.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })

def references (source : HavingFieldValueList) : List HavingPresenceRef :=
  source.presenceSlots.flatMap (·.references)

/-- The value domain changes the cell reader; the shared membership stream owns expansion
and the ordinary selector owns phase order (spec/06 §B.3–B.5). -/
private def withOperands (source : HavingFieldValueList) (phase : Phase)
    (context : ResolvingCorrelationContext Error)
    (consume : {kind : ValueListKind} → {Ref : Type} →
      (Ref → HavingOrigin) → (Ref → FieldId) → (Env → Ref → Except Error (ValueListCell kind)) →
      List (HavingFieldListSlot Ref) →
      Sum (List (HavingFieldListSlot Ref)) (List (ValueListAtom kind)) → Except Error Result) : Except Error Result :=
  match source with
  | .number subjects members => consume (kind := .number) (Ref := HavingNumberRef) (·.origin) (·.field.id)
      (fun env ref => ref.readValueListCell phase (fun _ => context.read env)) subjects (.inl members)
  | .token subjects members => consume (kind := .token) (Ref := HavingStringRef) (·.origin) (·.field.id)
      (fun env ref => ref.readValueListCell phase (fun _ => context.read env)) subjects (.inl members)
  | .tokenLiterals subjects members => consume (kind := .token) (Ref := HavingStringRef) (·.origin) (·.field.id)
      (fun env ref => ref.readValueListCell phase (fun _ => context.read env)) subjects (.inr members)

def evalValidationRead (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict :=
  source.withOperands .validation context fun origin field read subjects members => do
    let resolve := HavingMembershipStream.resolveSlots origin field read context frame
    let quantifier := match operator with | .scalar op => op.quantifier | .quantified op => op
    let (subjects, members) ← quantifier.resolveSidesOrdered (fun _ => resolve subjects) (fun _ =>
      match members with
      | .inl slots => resolve slots
      | .inr values => pure (values.map fun value => {
          cells := [.present value], hasUninstantiatedTail := false, hasHaving := false }))
    pure (quantifier.evalOrdered subjects members)

def evalComputationRead (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ComputationConditionResult :=
  source.withOperands .computation context fun origin field read subjects members =>
    operator.evalUsing (fun _ => match members with
      | .inl slots => HavingMembershipStream.collectSlots origin field read context frame slots
      | .inr values => pure (.ok values.reverse))
      (HavingMembershipStream.anySlots origin field read context frame subjects)

def evalValidation (source : HavingFieldValueList) (operator : ComputationValueListOperator)
    (context : CorrelationContext) (frame : CorrelationFrame) : Verdict :=
  match source.evalValidationRead operator context.asResolving frame with
  | .ok result => result
  | .error _ => .unknown

end HavingFieldValueList
end A12Kernel
