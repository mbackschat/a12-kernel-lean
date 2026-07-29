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

/-- Calendar unit shared by checked `AddDays`, `AddMonths`, and `AddYears` consumers. -/
inductive DateShiftUnit where
  | days
  | months
  | years
  deriving Repr, DecidableEq

/-- Authored position of a checked shift result in one bounded binary difference. -/
inductive ShiftDifferencePosition where
  | first
  | second
  deriving Repr, DecidableEq

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

/-- Whether this checked amount reads one Number field. Expression amounts include every checked direct-Number atom. -/
def referencesField (amount : CheckedTemporalShiftAmount model)
    (field : FieldId) : Bool :=
  match amount with
  | .literal _ => false
  | .field source _ => source.id == field
  | .expression checked _ =>
      checked.core.anyAtom (·.referencesField model field)

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

/-- Static refusal while resolving one checked direct-Number temporal shift amount. -/
inductive TemporalShiftAmountElabError where
  | field (error : ResolveError)
  | fieldNotNumber (field : FieldId)
  | expression (error : NumericValidationElabError)
  | expressionNotDirectNumber
  | incoherentCore
  deriving Repr, DecidableEq

/-- Resolve one ordinary nonrepeatable Number field as a temporal shift amount. -/
def elaborateTemporalFieldShiftAmount
    (model : FlatModel) (amountField : FieldId) :
    Except TemporalShiftAmountElabError
      (CheckedTemporalShiftAmount model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById amountField |>.mapError .field
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.fieldNotNumber amountField)
  if hAdmitted :
      model.admitsTemporalShiftAmountSource source = true then
    pure (.field source hAdmitted)
  else
    throw .incoherentCore

/-- Resolve one checked same-group numeric operation and retain only the direct Number-field atom subset audited for temporal shifting. -/
def elaborateTemporalExpressionShiftAmount
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) :
    Except TemporalShiftAmountElabError
      (CheckedTemporalShiftAmount model) := do
  let checked ← elaborateNumericValidationExpression model rowGroup surface
    |>.mapError .expression
  if hDirect :
      NumericValidationExpression.usesOnlyDirectNumberFields
        checked.core = true then
    pure (.expression checked hDirect)
  else
    throw .expressionNotDirectNumber

end A12Kernel
