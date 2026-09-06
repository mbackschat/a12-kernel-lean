import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenDistinctCount

/-! # A12Kernel.Conformance.HavingFilterDiagnostic — the `Having` filter's refusal classes

A `Having` filter's own refusals had **no** diagnostic projection at all, so eight carriers wrapping
`CorrelationElabError` dropped every one of them. The open question was whether the class belongs to
the filter or to the operator that wraps it, and it is answered by crossing rather than sampling:
fourteen filters against three carriers — a temporal extremum, a distinct count, and a filled-field
count — produced the identical class in every cell
([checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes)). One shared
projection is therefore right, and a per-carrier table would have been three copies of one fact.

The comparison rows are the reason the two arms carry the field's kind. A **numeric** comparison
collapses every non-Number, non-temporal kind into one class; a **String-literal** comparison spreads
the same kinds across four, and that column is the shared literal-comparison ladder's `stringLike` row cell
for cell — the same Kernel vocabulary reached through a generated equality. Either column read off
the other is wrong for six kinds of eight, which is what these rows lock.
-/

namespace A12Kernel.Conformance.HavingFilterDiagnostic

open A12Kernel

private def kinds : List SurfaceScalarKind :=
  [.number, .string, .temporal .date, .temporal .time,
    .boolean, .confirm, .enumeration, .dateRange]

/- **The numeric-comparison column.** Number is admitted, both temporal families draw the date
   class, and the other five collapse into one. That collapse is the whole content of the row: it is
   what the literal column below does *not* do. -/
example : kinds.map numericComparisonDiagnostic? =
    [ none
    , some .invalidTypeForComparison
    , some .invalidCompareToDate, some .invalidCompareToDate
    , some .invalidTypeForComparison, some .invalidTypeForComparison
    , some .invalidTypeForComparison, some .invalidTypeForComparison ] := by
  native_decide

/- **The String-literal column**, which is the shared ladder's `stringLike` row. String is admitted
   and Enumeration is gated on the literal's membership in the declared domain rather than on kind,
   so both project nothing; the other six spread across four classes where the numeric column had
   one. -/
example : kinds.map (literalComparisonDiagnostic? .stringLike) =
    [ some .invalidCompareToEnumOrString
    , none
    , some .invalidCompareToDate, some .invalidCompareToDate
    , some .invalidCompareToYesNo, some .invalidCompareToYes
    , none
    , some .invalidCompareToDateRange ] := by
  native_decide

/- **The two columns disagree on six of the eight kinds**, asserted directly so that collapsing them
   is a failing change rather than a silent one. They agree only on the two temporal families —
   every other kind, including the ones each column admits, is decided differently. -/
example : (kinds.filter (fun kind =>
    numericComparisonDiagnostic? kind != literalComparisonDiagnostic? .stringLike kind)).length
      = 6 := by
  native_decide

/- **The three scope classes separate.** A root-level field the filter's star cannot bind, a
   different repeatable group's field read without a star, and a star written inside the filter each
   report their own class — and the first two are the pair most easily collapsed, since both are
   "the filter read something its iteration does not cover". -/
example : [CorrelationElabError.fieldOutsideGroup .inner ["Probe", "Amount"] ["Probe", "Rows"],
    .fieldOutsideEnvironment .inner ["Probe", "Other", "OtherVal"] [] [0],
    .wildcardOnRuleGroup].map CorrelationElabError.diagnostic? =
    [ some .noIterationForWildcard
    , some .invalidIterationInFilterCondition
    , some .noWildcardsAllowed ] := by
  native_decide

/- The scale gate is the filter's too, and it is a live pair rather than a one-sided refusal: the
   same literal is admitted against a declaration whose scale fits. -/
example : (CorrelationElabError.equalityScaleMismatch ["Probe", "Rows", "RowVal"] 0
    ["Probe", "Rows", "RowScaled"] 2).diagnostic? =
    some .invalidCompareDecimalPlaces := by
  native_decide

/- **The exact Kernel identifiers** for the three classes this capsule adds, so they are pinned to
   the observable strings. The singular `TYPE` is not a typo and not the plural neighbour: the two
   are different Kernel constants reached by different gates. -/
example : [KernelStaticDiagnostic.invalidTypeForComparison,
    .invalidTypesForComparison, .noIterationForWildcard,
    .invalidIterationInFilterCondition].map KernelStaticDiagnostic.kernelCode =
    ["MVK_INVALID_TYPE_FOR_COMPARISON", "MVK_INVALID_TYPES_FOR_COMPARISON",
      "MVK_NO_ITERATION_FOR_WILDCARD",
      "MVK_INVALID_ITERATION_IN_FILTER_CONDITION"] := by
  native_decide

/- **The class survives the wrapping carrier**, which is the whole point of projecting it once. Two
   structurally different wrappers — a token distinct count and a Number uniqueness overload, the
   latter reaching the filter through its star operand rather than directly — report the filter's
   own class for the same refusal. A carrier that drops it instead reports nothing, which reads as
   "no class established" and is what these rows exist to prevent. -/
example : (TokenDistinctCountElabError.source
      (.having .wildcardOnRuleGroup)).diagnostic? =
    some .noWildcardsAllowed := by
  native_decide

example : (NumberValuesNotUniqueElabError.source
      (.star (.having (.fieldNotNumber ["Probe", "Rows", "RowText"] .string)))).diagnostic? =
    some .invalidTypeForComparison := by
  native_decide

end A12Kernel.Conformance.HavingFilterDiagnostic
