import A12Kernel.Elaboration.ErrorTextParameterAddressing

/-! # Locks on the message parameter's addressing gates

All five classes are source-derived and unwitnessed, which the owning module states as one block rather
than per class. These cases therefore lock the chosen account's internal shape, not a kernel
correspondence.

The matrix separates the literal `1` from a numeral of the same value, the bound check from the
maximum-of-one check, the symbolic specifier's escape, the two coordinates reporting one shape under two
names, the star gate's model-kind dependence against the declaration gate's independence, the
declaration gate's String precondition, and the relative-path boundary from both sides.
-/

namespace A12Kernel.Conformance.ErrorTextParameterAddressing

open A12Kernel

private def key? (coordinate : FormCoordinate) (declaredMax : Nat)
    (specifier : CoordinateSpecifier) : Option String :=
  (coordinateRefusal coordinate declaredMax specifier).map KernelStaticDiagnostic.kernelCode

private def valueKey? (kind : ModelKind) (access : ValueAccess) : Option String :=
  (valueAccessRefusal kind access).map KernelStaticDiagnostic.kernelCode

private def upKey? (level upCount : Nat) : Option String :=
  (relativeUpRefusal level upCount).map KernelStaticDiagnostic.kernelCode

/- **The special case is a spelling.** At a declared maximum of one the literal is admitted and a numeral
   denoting the same value is refused; above one both are admitted, so the divergence belongs to the
   maximum-of-one row and is not a general property of the two spellings. -/
example :
    key? .serial 1 .one = none ∧
      key? .serial 1 (.numeral 1) = some "INVALID_FIELD_L" ∧
      key? .serial 5 .one = none ∧
      key? .serial 5 (.numeral 1) = none := by
  native_decide

/- **The bound check is separate from the maximum-of-one check.** Above one a numeral is refused only
   past the maximum, and the maximum itself is admitted — the off-by-one the comparison invites. -/
example :
    key? .serial 5 (.numeral 5) = none ∧
      key? .serial 5 (.numeral 6) = some "INVALID_FIELD_L" ∧
      key? .serial 1 (.numeral 6) = some "INVALID_FIELD_L" := by
  native_decide

/- **A symbolic specifier escapes the bound but not the maximum-of-one check**, so it is refused in
   exactly one of the two situations a numeral is. -/
example :
    key? .serial 1 .symbolic = some "INVALID_FIELD_L" ∧
      key? .serial 5 .symbolic = none := by
  native_decide

/- **One mechanism, two names.** The line coordinate reproduces every row above under its own class, so
   nothing distinguishes the two beyond the code. -/
example :
    key? .line 1 .one = none ∧
      key? .line 1 (.numeral 1) = some "INVALID_FIELD_Z" ∧
      key? .line 5 (.numeral 6) = some "INVALID_FIELD_Z" ∧
      key? .line 5 .symbolic = none := by
  native_decide

/- **The star gate belongs to the A12 world**, and the declaration gate does not depend on the world at
   all — the pair of rows that keeps the model kind from being read as a permissiveness ordering. -/
example :
    valueKey? .a12 { referencedWithoutStar := false } =
        some "PARAM_VALUE_WITH_STARREFERENCE" ∧
      valueKey? .hModel { referencedWithoutStar := false } = none ∧
      valueKey? .a12 { fieldIsString := true, noValueValidation := true } =
        some "INVALID_NO_VALUE_VALIDATION" ∧
      valueKey? .hModel { fieldIsString := true, noValueValidation := true } =
        some "INVALID_NO_VALUE_VALIDATION" := by
  native_decide

/- **The star gate runs first**, so a field offending both reports the star class and only on A12; the
   same field on an H-model falls through to the declaration class. -/
example :
    valueKey? .a12 { referencedWithoutStar := false, fieldIsString := true,
                     noValueValidation := true } = some "PARAM_VALUE_WITH_STARREFERENCE" ∧
      valueKey? .hModel { referencedWithoutStar := false, fieldIsString := true,
                          noValueValidation := true } = some "INVALID_NO_VALUE_VALIDATION" := by
  native_decide

/- **The declaration class needs the String kind**, so the flag alone does not reach it — the row that
   keeps the gate from being read as kind-agnostic. -/
example :
    valueKey? .a12 { fieldIsString := false, noValueValidation := true } = none ∧
      valueKey? .a12 { fieldIsString := true, noValueValidation := false } = none ∧
      valueKey? .a12 {} = none := by
  native_decide

/- **The relative-path boundary, from both sides.** Climbing to the root group exactly is admitted and
   one step further is refused, at two different levels so the rule is not read off a single depth. -/
example :
    upKey? 2 2 = none ∧ upKey? 2 3 = some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS" ∧
      upKey? 0 0 = none ∧ upKey? 0 1 = some "ERROR_TEXT_PARAMETER_TOO_MANY_PARENT_GROUPS" ∧
      upKey? 5 1 = none := by
  native_decide

end A12Kernel.Conformance.ErrorTextParameterAddressing
