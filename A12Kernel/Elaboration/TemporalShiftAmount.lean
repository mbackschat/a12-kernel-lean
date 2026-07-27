import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.NumericValidation.Evaluation

/-! # Checked temporal shift amounts

This module owns the numeric operand boundary shared by checked Date and DateTime shifts.
It admits authored literals, ordinary nonrepeatable Number fields, and checked same-group
numeric expressions over only those fields. Evaluation retains directional fillability,
exact formal causes, arithmetic domain failure, and structural document failure; temporal
consumers decide how those distinctions affect their own result domains.
-/

namespace A12Kernel

/-- Truncate like `BigDecimal.intValue`, then retain the low signed 32 bits rather than saturating or rejecting a large temporal-shift amount. -/
def temporalShiftAmountToInt32 (value : Rat) : Int :=
  let truncated := if value < 0 then value.ceil else value.floor
  let modulus : Int := 4294967296
  let signBit : Int := 2147483648
  let lowBits := truncated % modulus
  if lowBits < signBit then lowBits else lowBits - modulus

/-- Whether one resolved declaration is an ordinary nonrepeatable Number source admitted as a temporal shift amount. -/
def FlatModel.admitsTemporalShiftAmountSource
    (model : FlatModel) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some source

/-- Whether every atom in one checked numeric operation is an ordinary Number field. This retains the audited phase-sensitive read class without introducing a temporal expression tree. -/
def NumericValidationExpression.usesOnlyDirectNumberFields
    (expression : NumericValidationExpression) : Bool :=
  AuthoredNumericExpr.allAtoms (fun
    | .field _ => true
    | _ => false) expression

/-- One statically checked temporal shift amount. Expressions reuse the shared numeric carrier and retain a certificate that every atom has the direct-Number interpretation audited for this consumer boundary. -/
inductive CheckedTemporalShiftAmount (model : FlatModel) where
  | literal (amount : Rat)
  | field (source : FlatNumberField)
      (sourceAdmitted :
        model.admitsTemporalShiftAmountSource source = true)
  | expression (checked : CheckedNumericValidationExpression model)
      (usesOnlyDirectNumberFields :
        NumericValidationExpression.usesOnlyDirectNumberFields
          checked.core = true)

namespace CheckedTemporalShiftAmount

/-- Evaluate a checked amount after its temporal source has been reached. Document failure stays structural; numeric missingness, formal causes, and arithmetic domain failure remain in the shared numeric result. -/
def read (amount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except CheckedDocumentError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
  match amount with
  | .literal value => pure (.ok (.value value .fixed))
  | .field source _ => do
      let cell ← input.read {
        field := source.id
        path := []
      }
      pure ((observeCell phase cell).asDirectNumericComparisonOperand source.info
        |>.toValidationArithmetic)
  | .expression checked _ =>
      pure (checked.evalWith fun
        | .field source =>
            (input.flatContext.resolveNumberComparisonOperandAt phase source)
              |>.toValidationArithmetic
        | _ => .error .groupState)

end CheckedTemporalShiftAmount

end A12Kernel
