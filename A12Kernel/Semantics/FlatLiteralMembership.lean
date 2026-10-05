import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel

/-- Scalar literal membership retains the subject's checked domain; unlike comparison, an empty
Number subject contributes no zero and a String literal list retains its empty token (spec/06 §B.4). -/
inductive FlatLiteralMembership where
  | number (field : FlatNumberField) (values : List Int)
  | token (operand : FlatTextFieldOperand) (values : List String)
  deriving Repr, DecidableEq

namespace FlatLiteralMembership

def field : FlatLiteralMembership → FlatField
  | .number field _ => .number field
  | .token operand _ => operand.field

def condition (operator : ValueListMembershipOp) : FlatLiteralMembership → FlatConditionLeaf
  | .number field values => .numberValueList operator.quantifier [field]
      (.literals (values.map Rat.ofInt)) .membership
  | .token operand values => .tokenValueList operator.quantifier [operand] (.literals values) .membership

def evalValidation (source : FlatLiteralMembership) (operator : ValueListMembershipOp)
    (cell : CheckedCell) : Verdict :=
  (source.condition operator).evalSelected { read := fun _ => cell }

/-- Literal members cannot fail; the shared scalar selector still reads the subject even for an
empty member set, preserving computation poison instead of comparison's empty substitution. -/
def evalComputation (source : FlatLiteralMembership) (operator : ValueListMembershipOp)
    (cell : CheckedCell) : ComputationConditionResult :=
  match source with
  | .number field values => operator.evalComputation
      [{ cells := [field.valueListCellAt .computation { read := fun _ => cell }],
         hasUninstantiatedTail := false, hasHaving := false }]
      [{ cells := values.map (fun value => .present (Rat.ofInt value)),
         hasUninstantiatedTail := false, hasHaving := false }]
  | .token operand values => operator.evalComputation
      [{ cells := [operand.checkedValueListCellAt .computation cell],
         hasUninstantiatedTail := false, hasHaving := false }]
      [{ cells := values.map .present, hasUninstantiatedTail := false, hasHaving := false }]

end FlatLiteralMembership
end A12Kernel
