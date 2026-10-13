import A12Kernel.Semantics.FullDateInputFormat

/-! # The temporal field-format vocabulary

A Date, Time, DateTime or DateFragment declaration names its format, and the Kernel admits one
vocabulary of thirteen formats whatever the kind: `yyyy-MM-dd`, `dd.MM.yyyy`, `yyyyMMdd`, `yyyy`,
`yyyy-MM`, `yyyyMM`, `MM`, `MM-dd`, `MMdd`, `ddMM`, `HH:mm:ss`, `yyyy-MM-dd'T'HH:mm:ss` and `dd.MM.`
([spec/05 §1](../../spec/05-dates-and-time.md)). The vocabulary is the union of the formats the four
bounded format owners classify, so there is no fifth list to keep in step: the three complete-Date
spellings, the eight component-omitting ones, the whole-second clock and the ISO whole-second DateTime.

The gate is kind-independent: a Time declaration is admitted `yyyy-MM-dd`, and the day-first
`dd.MM.yyyy'T'HH:mm:ss`, which tags DateTime-valued expressions, is refused on every kind. Whether an
absent format is admitted, as its kind's default, is the caller's question.
-/

namespace A12Kernel

/-- Whether the declared format is in the thirteen-format vocabulary. -/
def temporalDeclarationFormatAdmitted (format : String) : Bool :=
  (FullDateInputFormat.ofSource? format).isSome || (OmittingDateFormat.ofSource? format).isSome ||
    (TimeTargetFormat.ofSource? format).isSome || (DateTimeTargetFormat.ofSource? format).isSome

end A12Kernel
