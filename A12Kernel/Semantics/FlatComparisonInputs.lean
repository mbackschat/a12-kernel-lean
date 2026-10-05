import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.ScalarEquality

namespace A12Kernel

/-- Operand-side inventories keep identical field IDs distinct until their environments are selected. -/
def FlatComparison.inputFields : FlatComparison → List FlatField × List FlatField
  | .booleanFields _ left right => ([left.field], [right.field])
  | .textFields _ left right => ([left.field], [right.field])
  | .temporal _ left right => (left.fields, right.fields)
  | .time _ left right => ([.temporal left], [.temporal right])
  | comparison => (comparison.fields, [])

/-- Separate operand readers preserve candidate/captured identity even when both sides name the
same field. The consumer owns validation's eager reads or computation's poison short-circuit
(spec/02, spec/07); unsupported comparison families remain explicit. -/
def FlatComparison.foldSimpleReads {Error Result : Type}
    (comparison : FlatComparison) (phase : Phase)
    (readLeft readRight : FieldId → Except Error CheckedCell)
    (consume : {α : Type} → (α → α → Bool) → Except Error (SimpleComparisonOperand α) →
      (Unit → Except Error (SimpleComparisonOperand α)) → Except Error Result) :
    Option (Except Error Result) :=
  let text (read : FieldId → Except Error CheckedCell) (operand : FlatTextFieldOperand) := do
    let cell ← read operand.field.id
    pure (match operand.checkedValueListCellAt phase cell with
      | .empty => .notEvaluated
      | .present value => .value value true
      | .unknown cause => .unknown cause)
  let boolean (read : FieldId → Except Error CheckedCell) (operand : FlatBooleanOperand) := do
    let cell ← read operand.field.id
    pure (operand.resolveAt phase { read := fun _ => cell })
  let compare {α : Type} [BEq α] (op : EqualityOp) := consume (α := α) (fun a b => op.holds (a == b))
  match comparison with
  | .boolean op field expected => some (compare op (boolean readLeft (.boolean field)) (fun _ => pure (.value expected true)))
  | .confirm op field => some (compare op (boolean readLeft (.confirm field)) (fun _ => pure (.value true true)))
  | .booleanFields op left right => some (compare op (boolean readLeft left) (fun _ => boolean readRight right))
  | .string op field expected => some (compare op (text readLeft (.string field))
      (fun _ => pure (if expected.isEmpty then .notEvaluated else .value expected true)))
  | .enumeration op operand expected => some (compare op (text readLeft (.enumeration operand))
      (fun _ => pure (.value expected true)))
  | .textFields op left right => some (compare op (text readLeft left) (fun _ => text readRight right))
  | .number _ _ _ | .stringLength _ _ _ | .temporal _ _ _ | .time _ _ _ => none

/-- Validation reaches both addressed operands before projecting formal invalidity to UNKNOWN. -/
def FlatComparison.evalSimpleValidationReads (comparison : FlatComparison)
    (readLeft readRight : FieldId → Except Error CheckedCell) : Except Error Verdict :=
  (comparison.foldSimpleReads .validation readLeft readRight fun holds left right => do
    let left ← left
    let right ← right ()
    pure (evalSymmetricComparison holds left right)).getD (.ok .unknown)

def FlatComparison.evalSimpleComputationReads (comparison : FlatComparison)
    (readLeft readRight : FieldId → Except Error CheckedCell) :
    Except Error ComputationConditionResult :=
  (comparison.foldSimpleReads .computation readLeft readRight
    evalComputationComparisonExcept).getD (.ok .notTrue)

end A12Kernel
