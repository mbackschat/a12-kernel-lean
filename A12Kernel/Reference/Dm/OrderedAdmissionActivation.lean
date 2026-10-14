import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Reference.Dm.HavingScalarAdmission

/-! # Which authored texts need ordered admission

Syntax-only predicates over the parse tree that decide whether a text is walked in authored read order
before lowering, and what that walk must retain: a filter anywhere, a condition where the grammar
admits only an operation, an authored scalar slot, and projected target identity. They resolve
nothing, so activating the walk cannot itself reorder a read failure (spec/07 §3, spec/12 §12.3).
-/

namespace A12Kernel.Dm

mutual
/-- Traverse authored references, including keys, scopes and range endpoints, without resolving
or lowering them. Admission activation must not itself reorder read failures (spec/07 §3). -/
private partial def Expr.anyReference (test : Reference → Bool) (callTest : String → Bool := fun _ => false) : Expr → Bool
  | .entity reference | .value reference => reference.anyReference test callTest
  | .arith _ left right | .compare _ left right => left.anyReference test callTest || right.anyReference test callTest
  | .braces body | .parens body => body.anyReference test callTest
  | .logic _ parts => parts.any (Expr.anyReference test callTest)
  | .call name arguments listed scope =>
      callTest name ||
      arguments.any (Argument.anyReference test callTest) || (listed.getD []).any (Argument.anyReference test callTest) ||
        scope.any (Reference.anyReference test callTest)
  | _ => false

private partial def Reference.anyReference (test : Reference → Bool) (callTest : String → Bool := fun _ => false) (reference : Reference) : Bool :=
  test reference || reference.filter.any (Expr.anyReference test callTest) || match reference.index with
    | some (.reference key) => key.anyReference test callTest
    | _ => false

private partial def Argument.anyReference (test : Reference → Bool) (callTest : String → Bool := fun _ => false) : Argument → Bool
  | .mk expression rangeEnd => expression.anyReference test callTest || rangeEnd.any (Expr.anyReference test callTest)
end

/-- Activate ordered admission across an entire filter-containing expression, including its
preceding operands and separate lists (spec/07 §3). -/
def Expr.hasHaving : Expr → Bool := Expr.anyReference (·.filter.isSome)
def Reference.hasHaving : Reference → Bool := Reference.anyReference (·.filter.isSome)
def Argument.hasHaving : Argument → Bool := Argument.anyReference (·.filter.isSome)

def Expr.isConditionCall : Expr → Bool
  | .call id .. => conditionCallIds.contains id
  | _ => false

/-- A condition where the grammar admits only an operation: a comparison or connective as an operation
call's operand (`Abs`, `Min`, `Max`, a rounding or a numeric field form), or a condition call as such an
operand, an arithmetic operand or a comparison side. -/
private partial def Expr.hasConditionAsOperationOperand : Expr → Bool
  | .call id arguments listed _ =>
      let operation := id == "Abs" || id == "Min" || id == "Max" ||
        (roundingMode? id).isSome || isNumericFieldForm id
      let condition : Expr → Bool
        | .compare .. | .logic .. => true
        | operand => operand.isConditionCall
      let nested (argument : Argument) : Bool := match argument with
        | .mk operand rangeEnd => operand.hasConditionAsOperationOperand ||
            (rangeEnd.map (·.hasConditionAsOperationOperand)).getD false
      let operandIsCondition (argument : Argument) : Bool := match argument with
        | .mk operand _ => condition operand
      (operation && arguments.any operandIsCondition) || arguments.any nested || (listed.getD []).any nested
  | .compare _ left right | .arith _ left right =>
      left.isConditionCall || right.isConditionCall ||
        left.hasConditionAsOperationOperand || right.hasConditionAsOperationOperand
  | .logic _ parts => parts.any (·.hasConditionAsOperationOperand)
  | .braces body | .parens body => body.hasConditionAsOperationOperand
  | _ => false

/-- Authored scalar slots, lists and repetition operands need their parse/read diagnostics before
lowering loses their shape (spec/07 §5–6, spec/08 CurrentRepetition cascade; KF532). -/
def Expr.needsOrderedAdmission (expression : Expr) : Bool :=
  expression.hasHaving || expression.hasConditionAsOperationOperand || expression.anyReference (fun _ => false)
    (fun name => name == "Date" || name == "Time" || name == "CurrentRepetition" ||
      name == "RepetitionNotUnique" || name == "FirstFilledValue" ||
      (rawScalarOperator? name).isSome)

/-- Retain projected target identity across all authored fragments before alternative lowering
(spec/09 §6, self-read alternative-walk matrix). Parse-time admission still runs before refusal. -/
def Expr.hasProjectedReferenceTo (expression : Expr) (model : FlatModel)
    (group : GroupPath) (target : FieldId) : Bool :=
  let namesTarget := fun reference : Reference =>
    reference.path.toFieldPath?.any fun path =>
      (model.resolveFieldDeclarationUnchecked group path).toOption.any (·.id == target)
  expression.anyReference fun reference =>
    ((reference.index.isSome || reference.category.isSome) && namesTarget reference) ||
      match reference.index with
      | some (.reference key) => key.anyReference namesTarget
      | _ => false

def Expr.hasIndex : Expr → Bool := Expr.anyReference (·.index.isSome)

end A12Kernel.Dm
