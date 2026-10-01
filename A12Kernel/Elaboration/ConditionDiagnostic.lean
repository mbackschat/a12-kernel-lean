import A12Kernel.Elaboration.RawString
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.EnumerationComparability

/-! # The Kernel class of a flat rule condition's refusal

One projection for the flat condition elaborator's refusals, measured on the plain rule comparison
[checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection).
Most arms delegate to the mechanism that already carries the measured table — the resolver's classes,
the literal ladder, the rule comparison's kind arm, and the Enumeration display arm — and the few that
answer with one constant are single measured rows.

The projection answers only for a condition built from the **measured shapes**: a comparison under `==`,
`Length` under `>` or `==`, a filled test, and the connectives. The error alone cannot carry that
restriction. The kind arms carry no operator, and the Kernel selects a different gate under an ordering
([`kf270`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf270)). One error arm is also raised by value
lists and the alternative Enumeration surface with its two kinds meaning something else. -/

namespace A12Kernel

namespace ElabError

/-- The literal ladder's family for a literal of this kind. -/
private def literalFamily : SurfaceScalarKind → ComparedLiteralFamily
  | .number => .number
  | .boolean | .confirm => .booleanLike
  | .temporal _ => .temporal
  | .string | .enumeration | .dateRange => .stringLike

/-- The class one refusal arm draws on the measured shapes, or `none` where this fragment's refusal is
its own boundary or the arm is unmeasured. `none` never means acceptance. It is private because the
error does not say which shape raised it; `SurfaceCondition.refusalDiagnostic?` supplies that gate.

Two arms are deliberately left out. A same-kind Number, DateRange or Boolean field pair, and a Number
pair of different scales, is a refusal of this flat route: the Kernel admits the first three and answers
the last with the scale class. And a clock literal meets the date-literal component gate, whose Kernel
class depends on the field it meets — admitted on a Time field, the date class on a Date or DateTime
one — which the error does not carry. -/
private def armDiagnostic? : ElabError → Option KernelStaticDiagnostic
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

/-- Whether every comparison in a condition has a shape the class grid measured: a comparison or a
point-in-time or Base Year partner under `==`, and `Length` under `>` or `==`. A value list, a
membership, the category-read and alternative Enumeration surfaces, and every other operator fall
outside, since each either draws a class the arms below would misname or has no retained row. -/
def SurfaceCondition.hasMeasuredClassShape : SurfaceCondition → Bool
  | .compare op _ _ | .compareFields op _ _ | .compareToday op _ _ | .compareNow op _ _
  | .compareBaseYear op _ _ | .compareBaseYearRange op _ _ _ => op == .equal
  | .lengthCompare op _ _ => op == .greater || op == .equal
  | .fieldFilled _ | .fieldNotFilled _ => true
  | .and left right | .or left right => left.hasMeasuredClassShape && right.hasMeasuredClassShape
  | _ => false

/-- The Kernel class of the refusal `elaborate` raised for `condition`, or `none` where the condition
leaves the measured shapes or the arm is unmeasured. `none` never means acceptance. Which refusal a
condition with several failing comparisons reports first is Lean's left-to-right order, which no row
separates from the Kernel's. -/
def SurfaceCondition.refusalDiagnostic? (condition : SurfaceCondition) (error : ElabError) :
    Option KernelStaticDiagnostic :=
  if condition.hasMeasuredClassShape then error.armDiagnostic? else none

end A12Kernel
