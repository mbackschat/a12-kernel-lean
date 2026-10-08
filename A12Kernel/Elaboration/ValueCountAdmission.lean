import A12Kernel.Elaboration.Flat.Context

namespace A12Kernel

/-- Whether one field kind is legal for the authored Boolean constant. `True` admits Boolean and Confirm; `False` admits only Boolean. -/
def booleanValueCountKindAllowed (expected : Bool) : FieldKind → Bool
  | .boolean => true
  | .confirm => expected
  | _ => false

/-- String accepts every decoded literal; Enumeration requires membership in its exact selected stored/category domain. The gate reads one declaration beside the operand resolved from it, which is what lets a direct slot, a starred slot, and one member of a group expansion share it. -/
def FlatFieldDecl.allowsTokenValueCountLiteral (declaration : FlatFieldDecl)
    (operand : FlatTextFieldOperand) (expected : String) : Bool :=
  match operand with
  | .string _ => true
  | .enumeration source =>
      match declaration.enumeration with
      | some enumeration =>
          match source.projection with
          | .stored => enumeration.storedTokens.contains expected
          | .category mapping => mapping.categoryTokens.contains expected
      | none => false

end A12Kernel
