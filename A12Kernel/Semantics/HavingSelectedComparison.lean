import A12Kernel.Semantics.HavingFirstFilled
import A12Kernel.Semantics.DateRangeComparison

namespace A12Kernel

inductive HavingSelectedRef where
  | text (reference : HavingStringRef)
  | boolean (origin : HavingOrigin) (field : FlatBooleanField)
  | dateRange (origin : HavingOrigin) (field : FlatDateRangeField)
  deriving Repr, DecidableEq

def HavingSelectedRef.origin : HavingSelectedRef → HavingOrigin
  | .text reference => reference.origin
  | .boolean origin _ | .dateRange origin _ => origin

def HavingSelectedRef.fieldId : HavingSelectedRef → FieldId
  | .text reference => reference.field.id
  | .boolean _ field => field.id
  | .dateRange _ field => field.id

def HavingSelectedRef.presence (reference : HavingSelectedRef) : HavingPresenceRef :=
  { origin := reference.origin, field := reference.fieldId }

private def HavingSelectedRef.observe (reference : HavingSelectedRef) (phase : Phase)
    (cell : CheckedCell) : CellObservation :=
  match reference with
  | .text reference => match reference.operand.checkedValueListCellAt phase cell with
      | .present token => .value (.str token)
      | .empty => .empty
      | .unknown cause => .unknown cause
  | reference => match observeCell phase cell with
      | .value value => match reference, value with
          | .boolean _ _, .bool _ | .dateRange _ _, .dateRange _ => .value value
          | _, _ => .unknown .malformed
      | observation => observation

inductive HavingSelectedOperand where
  | field (reference : HavingSelectedRef)
  | firstFilled (slots : List (HavingFieldListSlot HavingSelectedRef))
  | text (value : String)
  | boolean (value : Bool)
  deriving Repr, DecidableEq

namespace HavingSelectedOperand

def referenceSlots : HavingSelectedOperand → List (HavingFieldListSlot HavingSelectedRef)
  | .field reference => [.direct reference]
  | .firstFilled slots => slots
  | .text _ | .boolean _ => []

def presenceSlots (operand : HavingSelectedOperand) : List (HavingFieldListSlot HavingPresenceRef) :=
  operand.referenceSlots.map (·.map HavingSelectedRef.presence)

/-- Selection uses the ordinary prefix state, including false-valued Boolean payloads; text
literals retain the selected-token comparison's empty suppression (spec/07 §5, spec/06). -/
def evaluate (operand : HavingSelectedOperand) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand Value) := do
  match operand with
  | .text value => pure (if value.isEmpty then .notEvaluated else .value (.str value) true)
  | .boolean value => pure (.value (.bool value) true)
  | .field reference =>
      pure (reference.observe phase (← context.read (frame.envAt reference.origin) reference.fieldId)).asValidationSimpleOperand
  | .firstFilled slots =>
      let result ← HavingFirstFilled.scanWith HavingSelectedRef.origin HavingSelectedRef.fieldId
        (fun state reference cell => scanFirstFilledObservations [reference.observe phase cell] state) context frame slots
      pure (match result with | .inl _ => .notEvaluated | .inr value => value)

end HavingSelectedOperand

structure HavingSelectedComparison where
  operator : EqualityOp
  left : HavingSelectedOperand
  right : HavingSelectedOperand
  deriving Repr, DecidableEq

namespace HavingSelectedComparison

def presenceSlots (source : HavingSelectedComparison) : List (HavingFieldListSlot HavingPresenceRef) :=
  source.left.presenceSlots ++ source.right.presenceSlots

def references (source : HavingSelectedComparison) : List HavingPresenceRef :=
  source.presenceSlots.flatMap (·.references)

private def sameValue : Value → Value → Bool
  | .str left, .str right => left == right
  | .bool left, .bool right => left == right
  | .dateRange left, .dateRange right => left.sameIdentity right
  | _, _ => false

def evalValidationRead (source : HavingSelectedComparison)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let left ← source.left.evaluate .validation context frame
  let right ← source.right.evaluate .validation context frame
  pure (source.operator.evalSymmetric sameValue left right)

def evalComputationRead (source : HavingSelectedComparison)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ComputationConditionResult :=
  evalComputationComparisonExcept (fun left right => source.operator.holds (sameValue left right))
    (source.left.evaluate .computation context frame) (fun _ => source.right.evaluate .computation context frame)

end HavingSelectedComparison
end A12Kernel
