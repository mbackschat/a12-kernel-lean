import A12Kernel.Semantics.HavingFieldValueList

namespace A12Kernel

/-- Direct uniqueness retains typed Number equality and exact token/temporal text identity
(spec/07 §5); temporal decoding must not erase distinct stored spellings. -/
inductive HavingUniqueness where
  | number (operands : List HavingNumberRef)
  | token (operands : List HavingStringRef)
  | temporal (operands : List HavingTemporalRef)
  deriving Repr, DecidableEq

namespace HavingUniqueness

def references : HavingUniqueness → List HavingPresenceRef
  | .number operands => operands.map fun ref => { origin := ref.origin, field := ref.field.id }
  | .token operands => operands.map fun ref => { origin := ref.origin, field := ref.field.id }
  | .temporal operands => operands.map fun ref => { origin := ref.origin, field := ref.field.id }

/-- Reuse the ordinary duplicate step, requesting only the deciding prefix. Validation's
skip rule is the sole phase adaptation; computation retains reached poison (spec/07 §5). -/
def scan (phase : Phase) (read : Operand → Except Error (ValueListCell kind))
    (seen : List (ValueListAtom kind)) : List Operand → Except Error ComputationConditionResult
  | [] => pure .notTrue
  | operand :: remaining => do
      let cell ← read operand
      let cell : ValueListCell kind := match phase, cell with
        | .validation, .unknown _ => .empty
        | _, cell => cell
      match cell.duplicateComputationStep seen with
      | .inl seen => scan phase read seen remaining
      | .inr (.ok ()) => pure .holds
      | .inr (.error cause) => pure (.poison cause)

def evalRead (source : HavingUniqueness) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult :=
  let read := fun origin => context.read (frame.envAt origin)
  match source with
  | .number operands => scan phase (fun ref => ref.readValueListCell phase read) [] operands
  | .token operands => scan phase (fun ref => ref.readValueListCell phase read) [] operands
  | .temporal operands => scan phase (kind := .token) (fun ref => do
      let cell ← read ref.origin ref.field.id
      match observeCell phase cell with
      | .empty => pure .empty
      | .unknown cause | .poison cause => pure (.unknown cause)
      | .value _ => match context.storedText (frame.envAt ref.origin) ref.field.id with
          | some text => pure (.present text)
          | none => throw (context.storedTextUnavailable ref.field.id)) [] operands

def evalValidationRead (source : HavingUniqueness)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  pure (match ← source.evalRead .validation context frame with
    | .holds => .fired .value
    | .notTrue => .notFired
    | .poison _ => .unknown)

end HavingUniqueness
end A12Kernel
