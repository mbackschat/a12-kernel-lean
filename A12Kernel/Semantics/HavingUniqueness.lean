import A12Kernel.Semantics.HavingFieldValueList
import A12Kernel.Semantics.HavingEntityList

namespace A12Kernel

/-- Uniqueness retains authored slots, typed Number equality and exact token/temporal text identity
(spec/07 §5); temporal decoding must not erase distinct stored spellings. -/
inductive HavingUniqueness where
  | number (operands : List (HavingFieldListSlot HavingNumberRef))
  | token (operands : List (HavingFieldListSlot HavingStringRef))
  | temporal (operands : List (HavingFieldListSlot HavingTemporalRef))
  deriving Repr, DecidableEq

namespace HavingUniqueness

def references : HavingUniqueness → List HavingPresenceRef
  | .number operands => (operands.flatMap (·.references)).map fun ref => { origin := ref.origin, field := ref.field.id }
  | .token operands => (operands.flatMap (·.references)).map fun ref => { origin := ref.origin, field := ref.field.id }
  | .temporal operands => (operands.flatMap (·.references)).map fun ref => { origin := ref.origin, field := ref.field.id }

def presenceSlots : HavingUniqueness → List (HavingFieldListSlot HavingPresenceRef)
  | .number slots => slots.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })
  | .token slots => slots.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })
  | .temporal slots => slots.map (·.map fun ref => { origin := ref.origin, field := ref.field.id })

def step (phase : Phase) (seen : List (ValueListAtom kind)) (cell : ValueListCell kind) :
    Sum (List (ValueListAtom kind)) ComputationConditionResult :=
  let cell : ValueListCell kind := match phase, cell with
    | .validation, .unknown _ => .empty
    | _, cell => cell
  match cell.duplicateComputationStep seen with
  | .inl seen => .inl seen
  | .inr (.ok ()) => .inr .holds
  | .inr (.error cause) => .inr (.poison cause)

/-- Reuse the ordinary duplicate step, requesting only the deciding prefix. Validation's
skip rule is the sole phase adaptation; computation retains reached poison (spec/07 §5). -/
def scan (phase : Phase) (read : Operand → Except Error (ValueListCell kind))
    (seen : List (ValueListAtom kind)) : List Operand → Except Error ComputationConditionResult
  | [] => pure .notTrue
  | operand :: remaining => do
      let cell ← read operand
      match step phase seen cell with
      | .inl seen => scan phase read seen remaining
      | .inr result => pure result

def scanSlots (phase : Phase) (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (read : Env → Ref → Except Error (ValueListCell kind))
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (operands : List (HavingFieldListSlot Ref)) : Except Error ComputationConditionResult := do
  match ← HavingFieldListSlot.foldRead origin field context frame
      (fun seen ref environment => step phase seen <$> read environment ref) [] operands with
  | .inl _ => pure .notTrue
  | .inr result => pure result

def evalRead (source : HavingUniqueness) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult :=
  match source with
  | .number operands => scanSlots phase (·.origin) (·.field.id)
      (fun environment ref => ref.readValueListCell phase (fun _ => context.read environment)) context frame operands
  | .token operands => scanSlots phase (·.origin) (·.field.id)
      (fun environment ref => ref.readValueListCell phase (fun _ => context.read environment)) context frame operands
  | .temporal operands => scanSlots phase (kind := .token) (·.origin) (·.field.id) (fun environment ref => do
      let cell ← context.read environment ref.field.id
      match observeCell phase cell with
      | .empty => pure .empty
      | .unknown cause | .poison cause => pure (.unknown cause)
      | .value _ => match context.storedText environment ref.field.id with
          | some text => pure (.present text)
          | none => throw (context.storedTextUnavailable ref.field.id)) context frame operands

def evalValidationRead (source : HavingUniqueness)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  pure (match ← source.evalRead .validation context frame with
    | .holds => .fired .value
    | .notTrue => .notFired
    | .poison _ => .unknown)

end HavingUniqueness
end A12Kernel
