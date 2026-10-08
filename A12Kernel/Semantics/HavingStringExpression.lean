import A12Kernel.Semantics.HavingSelectedComparison
import A12Kernel.Semantics.StringComputation

namespace A12Kernel

/-- String expressions retain per-occurrence correlation and the existing ordered selection
slots; neither a captured read nor a group expansion is flattened to a bare field id. -/
inductive HavingStringSource where
  | field (reference : HavingPresenceRef)
  | firstFilled (slots : List (HavingFieldListSlot HavingSelectedRef))
  deriving Repr, DecidableEq

def HavingStringSource.presenceSlots : HavingStringSource → List (HavingFieldListSlot HavingPresenceRef)
  | .field reference => [.direct reference]
  | .firstFilled slots => slots.map (·.map HavingSelectedRef.presence)

private def HavingStringSource.fieldId : HavingStringSource → FieldId
  | .field reference => reference.field
  | .firstFilled slots => (slots.flatMap (·.references)).head?.map HavingSelectedRef.fieldId |>.getD 0

/-- Number conversion consumes the document's formal-read text, never its raw spelling or a
re-rendered rational (spec/09 §3). Unavailable text is a structural capability failure. -/
def HavingStringSource.read (source : HavingStringSource) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand String) := do
  match source with
  | .firstFilled slots =>
      match ← (HavingSelectedOperand.firstFilled slots).evaluate phase context frame with
      | .value (.str text) given => pure (.value text given)
      | .value _ _ => throw context.stringExpressionUnavailable
      | .notEvaluated => pure .notEvaluated
      | .unknown cause => pure (.unknown cause)
  | .field reference =>
      let env := frame.envAt reference.origin
      match observeCell phase (← context.read env reference.field) with
      | .empty => pure .notEvaluated
      | .unknown cause | .poison cause => pure (.unknown cause)
      | .value (.num _) =>
          let some text := context.numberText env reference.field
            | throw (context.storedTextUnavailable reference.field)
          pure (.value text true)
      | .value (.str text) | .value (.enum text) =>
          pure (if text.isEmpty then .notEvaluated else .value text true)
      | .value _ => throw context.stringExpressionUnavailable

structure HavingStringComparison where
  operator : EqualityOp
  left : StringExpr HavingStringSource
  right : StringExpr HavingStringSource
  deriving Repr, DecidableEq

namespace HavingStringComparison

def presenceSlots (source : HavingStringComparison) : List (HavingFieldListSlot HavingPresenceRef) :=
  (source.left.fields ++ source.right.fields).flatMap HavingStringSource.presenceSlots

def references (source : HavingStringComparison) : List HavingPresenceRef :=
  source.presenceSlots.flatMap (·.references)

/-- The ordinary String tree owns concatenation, UTF-16 ranges and phase ordering. The two
error layers preserve caller read failures separately from unsupported String evaluation. -/
def operand (source : StringExpr HavingStringSource) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand String) := do
  let read (ref : HavingStringSource) : ExceptT StringComputationFault (Except Error) (SimpleComparisonOperand String) :=
    ExceptT.mk ((ref.read phase context frame).map Except.ok)
  let result ← (source.evalOperandWithSource HavingStringSource.fieldId phase read).run
  let result ← result.mapError (fun _ => context.stringExpressionUnavailable)
  pure (match result with | .value text _ => if text.isEmpty then .notEvaluated else result | _ => result)

def evalValidationRead (source : HavingStringComparison)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let left ← operand source.left .validation context frame
  let right ← operand source.right .validation context frame
  pure (source.operator.evalSymmetric (· == ·) left right)

def evalComputationRead (source : HavingStringComparison)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ComputationConditionResult :=
  evalComputationComparisonExcept (fun left right => source.operator.holds (left == right))
    (operand source.left .computation context frame) (fun _ => operand source.right .computation context frame)

end HavingStringComparison
end A12Kernel
