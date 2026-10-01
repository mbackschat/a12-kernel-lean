import A12Kernel.Elaboration.RawString
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.EnumerationComparability

/-! # The Kernel class of a flat rule condition's refusal

One projection for the flat condition elaborator's refusals, measured on the plain rule comparison
[checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection). It owns no class of its own: every arm delegates
to the mechanism that already carries the measured table — the resolver's classes, the literal
ladder, the rule comparison's kind arm, and the Enumeration display arm. -/

namespace A12Kernel

namespace ElabError

/-- The literal ladder's family for a literal of this kind. -/
private def literalFamily : SurfaceScalarKind → ComparedLiteralFamily
  | .number => .number
  | .boolean | .confirm => .booleanLike
  | .temporal _ => .temporal
  | .string | .enumeration | .dateRange => .stringLike

/-- The class a flat rule condition's refusal draws, or `none` where this fragment's refusal is its
own boundary or the arm is unmeasured. `none` never means acceptance.

Two arms are deliberately left out. A pair of fields of one kind outside the String, Enumeration and
temporal routes is a refusal of this flat route, which the Kernel admits. And a clock literal meets
the date-literal component gate, whose Kernel class depends on the field it meets — admitted on a Time
field, the date class on a Date or DateTime one — which the error does not carry. -/
def diagnostic? : ElabError → Option KernelStaticDiagnostic
  | .resolve error => error.diagnostic?
  | .literalKindMismatch _ field literal => literalComparisonDiagnostic? (literalFamily literal) field
  | .illegalConfirmLiteral _ => some .invalidCompareToYes
  | .temporalOperandKindMismatch _ _ left right =>
      (ruleComparisonKindArm? left right).map (·.diagnostic)
  | .temporalFormatsIncompatible _ _ | .temporalNowRequiresTime _ => some .invalidCompareToDate
  | .baseYearNotDeclared => some .conditionNoBaseYear
  | .baseYearScaleMismatch _ _ => some .invalidCompareDecimalPlaces
  | .lengthOperandKindMismatch _ _ => some .noString
  | .enumerationComparability _ _ error => some error.diagnostic
  | .enumerationOperand _ (.invalidLiteral _) => some .invalidStringConstantForEnumComparison
  | error@(.rawStringLength _) | error@(.rawStringLengthBound _) => error.rawStringDiagnostic?
  -- Named rather than wildcarded, so a new refusal must be classified: the rest are this fragment's
  -- boundaries, routing, or unmeasured on this carrier.
  | .unsupportedOperator _ | .temporalLiteralNeedsBaseYear _ | .invalidTemporalLiteralComponents _
  | .rawStringValue _ | .enumerationOperand _ (.unknownCategory _) | .textFieldOperandKindMismatch _ _
  | .emptyValueList _ | .groupOperandOutsideTokenRoute _ | .emptyValueListFields
  | .emptyValueListValueFields | .duplicateValueListField _ _ | .duplicateStringValueListField _
  | .duplicateNumberValueListField _ | .incoherentCore => none

end ElabError

end A12Kernel
