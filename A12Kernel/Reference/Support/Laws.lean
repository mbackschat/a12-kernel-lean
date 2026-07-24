import A12Kernel.Reference.Support.Manifest

/-! # Exhaustive support-vocabulary and manifest locks -/

namespace A12Kernel.Reference.Support

open Lean

private def tagsRoundTrip [BEq α] (values : List α) (tag : α → String)
    (fromTag? : String → Option α) : Bool :=
  values.all fun value => fromTag? (tag value) == some value

example (operation : Operation) : Operation.all.contains operation = true := by
  cases operation <;> native_decide

example (operator : ComparisonOperator) : ComparisonOperator.all.contains operator = true := by
  cases operator <;> native_decide

example (kind : FieldKindTag) : FieldKindTag.all.contains kind = true := by
  cases kind <;> native_decide

example (form : ConditionFormTag) : ConditionFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelatedHavingFormTag) :
    CorrelatedHavingFormTag.all.contains form = true := by
  cases form <;> native_decide

example (origin : HavingOriginTag) : HavingOriginTag.all.contains origin = true := by
  cases origin <;> native_decide

example (kind : LiteralKindTag) : LiteralKindTag.all.contains kind = true := by
  cases kind <;> native_decide

example (form : PathFormTag) : PathFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelationPathFormTag) :
    CorrelationPathFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelationStarPathFormTag) :
    CorrelationStarPathFormTag.all.contains form = true := by
  cases form <;> native_decide

example (scope : ReferencedScopeTag) : ReferencedScopeTag.all.contains scope = true := by
  cases scope <;> native_decide

example (form : RawCellFormTag) : RawCellFormTag.all.contains form = true := by
  cases form <;> native_decide

example (form : CorrelationCellFormTag) :
    CorrelationCellFormTag.all.contains form = true := by
  cases form <;> native_decide

example (cause : RejectedCauseTag) : RejectedCauseTag.all.contains cause = true := by
  cases cause <;> native_decide

example (verdict : VerdictTag) : VerdictTag.all.contains verdict = true := by
  cases verdict <;> native_decide

example (category : DiagnosticCategory) : DiagnosticCategory.all.contains category = true := by
  cases category <;> native_decide

example (code : DiagnosticCode) : DiagnosticCode.all.contains code = true := by
  cases code <;> native_decide

example (exclusion : KnownExclusion) : KnownExclusion.all.contains exclusion = true := by
  cases exclusion <;> native_decide

example : ComparisonOperator.supported = [.equal, .notEqual] := by
  native_decide

example : comparisonMatrix.map (·.fieldKind) = FieldKindTag.all := by
  native_decide

example : comparisonMatrix.all fun capability =>
    capability.operators == ComparisonOperator.supported := by
  native_decide

example : (Operation.all.map Operation.tag).Nodup ∧
    (ComparisonOperator.all.map ComparisonOperator.tag).Nodup ∧
    (FieldKindTag.all.map FieldKindTag.tag).Nodup ∧
    (ConditionFormTag.all.map ConditionFormTag.tag).Nodup ∧
    (CorrelatedHavingFormTag.all.map CorrelatedHavingFormTag.tag).Nodup ∧
    (HavingOriginTag.all.map HavingOriginTag.tag).Nodup ∧
    (LiteralKindTag.all.map LiteralKindTag.tag).Nodup ∧
    (PathFormTag.all.map PathFormTag.tag).Nodup ∧
    (CorrelationPathFormTag.all.map CorrelationPathFormTag.tag).Nodup ∧
    (CorrelationStarPathFormTag.all.map CorrelationStarPathFormTag.tag).Nodup ∧
    (ReferencedScopeTag.all.map ReferencedScopeTag.tag).Nodup ∧
    (RawCellFormTag.all.map RawCellFormTag.tag).Nodup ∧
    (CorrelationCellFormTag.all.map CorrelationCellFormTag.tag).Nodup ∧
    (RejectedCauseTag.all.map RejectedCauseTag.tag).Nodup ∧
    (VerdictTag.all.map VerdictTag.tag).Nodup ∧
    (DiagnosticCategory.all.map DiagnosticCategory.tag).Nodup ∧
    (DiagnosticCode.all.map DiagnosticCode.tag).Nodup ∧
    (KnownExclusion.all.map KnownExclusion.tag).Nodup := by
  native_decide

example : ComparisonOperator.all.all fun operator =>
    ComparisonOperator.fromTag? operator.tag == some operator := by
  native_decide

example : ComparisonOperator.all.all fun operator =>
    ComparisonOperator.ofSurface operator.toSurface == operator := by
  native_decide

example : tagsRoundTrip Operation.all Operation.tag Operation.fromTag? &&
    tagsRoundTrip FieldKindTag.all FieldKindTag.tag FieldKindTag.fromTag? &&
    tagsRoundTrip ConditionFormTag.all ConditionFormTag.tag ConditionFormTag.fromTag? &&
    tagsRoundTrip CorrelatedHavingFormTag.all CorrelatedHavingFormTag.tag
      CorrelatedHavingFormTag.fromTag? &&
    tagsRoundTrip HavingOriginTag.all HavingOriginTag.tag HavingOriginTag.fromTag? &&
    tagsRoundTrip LiteralKindTag.all LiteralKindTag.tag LiteralKindTag.fromTag? &&
    tagsRoundTrip PathFormTag.all PathFormTag.tag PathFormTag.fromTag? &&
    tagsRoundTrip CorrelationPathFormTag.all CorrelationPathFormTag.tag
      CorrelationPathFormTag.fromTag? &&
    tagsRoundTrip CorrelationStarPathFormTag.all CorrelationStarPathFormTag.tag
      CorrelationStarPathFormTag.fromTag? &&
    tagsRoundTrip ReferencedScopeTag.all ReferencedScopeTag.tag ReferencedScopeTag.fromTag? &&
    tagsRoundTrip RawCellFormTag.all RawCellFormTag.tag RawCellFormTag.fromTag? &&
    tagsRoundTrip CorrelationCellFormTag.all CorrelationCellFormTag.tag
      CorrelationCellFormTag.fromTag? &&
    tagsRoundTrip RejectedCauseTag.all RejectedCauseTag.tag RejectedCauseTag.fromTag? &&
    tagsRoundTrip VerdictTag.all VerdictTag.tag VerdictTag.fromTag? &&
    tagsRoundTrip DiagnosticCategory.all DiagnosticCategory.tag DiagnosticCategory.fromTag? &&
    tagsRoundTrip KnownExclusion.all KnownExclusion.tag KnownExclusion.fromTag? = true := by
  native_decide

example : ComparisonOperator.fromTag? "greaterEqual" = some .greaterEqual := by
  native_decide

example : FieldKindTag.fromTag? "number" = some .number := by
  native_decide

example : PathFormTag.classify (.relative 0) ["Child"] = none := by
  native_decide

example : PathFormTag.classify (.relative 1) ["Sibling"] = some .parentRelative := by
  native_decide

example : CorrelationPathFormTag.classify (.relative 0) ["Items"] =
    some .childRelative := by
  native_decide

example : CorrelationPathFormTag.classify (.relative 0) ["Sub", "Items"] = none := by
  native_decide

example : CorrelationPathFormTag.classify (.relative 0) [] = none := by
  native_decide

example : CorrelationStarPathFormTag.classify (.relative 0) [] =
    some .directChildRelative := by
  native_decide

example : CorrelationStarPathFormTag.classify (.relative 0) ["Sub"] = none := by
  native_decide

example : CorrelationCellFormTag.classify .parsedNumber none = some .parsedNumber := by
  native_decide

example : CorrelationCellFormTag.classify .rejected (some .malformed) =
    some .rejectedMalformed := by
  native_decide

example : CorrelationCellFormTag.classify .rejected (some .declaredConstraint) = none := by
  native_decide

example : ComparisonOperator.unsupported = [.less, .lessEqual, .greater, .greaterEqual] := by
  native_decide

example : (DiagnosticCode.all.map DiagnosticCode.category).eraseDups =
    DiagnosticCategory.all := by
  native_decide

end A12Kernel.Reference.Support
