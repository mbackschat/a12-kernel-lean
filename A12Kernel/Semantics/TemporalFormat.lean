import A12Kernel.Semantics.DateTimeComparison

/-! # Temporal format-component admission

This capsule owns the static component facts shared by direct temporal comparisons and temporal extrema plus the exact DateRange presentation discriminator shared by bounded input and target consumers. Direct comparisons preserve the original date-versus-time class, compare year presence after optional Base Year supplementation, and require matching time presence only for equality/inequality. Aggregate admission preserves that original class and additionally requires the complete supplemented component sets to match. Text parsing, scalar temporal format spelling, operand classification, and resolved value evaluation remain separate.
-/

namespace A12Kernel

/-- Parser-independent component shape of the two legal Date constants: `DD.MM.YYYY` and the Base-Year-dependent `DD.MM.` form. Lexical spelling and decoding are earlier responsibilities. -/
def TemporalComponents.isDateLiteral (components : TemporalComponents) : Bool :=
  components.month && components.day && !components.hasTime

/-- Static component identity carried by `Now`: a full date and time, independent of its exact millisecond runtime value. -/
def TemporalComponents.now : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

/-- Static identity of a complete calendar date with no time component. -/
def TemporalComponents.fullDate : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := false, minute := false, second := false }

/-- Static identity of a complete whole-second Time with no date component. -/
def TemporalComponents.time : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

/-- Static component identity carried by `Today`. -/
def TemporalComponents.today : TemporalComponents := TemporalComponents.fullDate

def TemporalComponents.baseYear : TemporalComponents := TemporalComponents.fullDate

/-- Which suffix of an otherwise complete Date may be unknown in stored form. The cases are ordered by increasing permitted uncertainty, but no Boolean collapse is sound: month-optional also permits an unknown day, and year-optional permits all three omissions. -/
inductive TemporalPartialMode where
  | full
  | dayOptional
  | monthOptional
  | yearOptional
  deriving Repr, DecidableEq

/-- Static incoherence in declaration-owned temporal target policy. Exact format syntax is checked before this parser-independent boundary; this layer preserves its source without trying to reconstruct it from component flags. -/
inductive TemporalTargetPolicyError where
  | emptyFormat
  | partialModeRequiresFullDate
  /-- The opt-in pre-1900 check on a declaration whose object carries no such property. The Kernel's
  `TimeType` and `DateTimeType` have only a format and annotations at 30.8.1, so the shape is
  rejected by the deserializer before any gate could find it inert — a schema fact rather than a
  behavioural rule, which is why the arm reads as a kind test and is nonetheless right. -/
  | youngerThan1900RequiresDate
  /-- The opt-in pre-1900 check on a Date declaration whose format carries **no year**. The Kernel
  refuses the model with `MVK_ADDITIONAL_CHECK_INVALID`, and its own message keys on the components —
  *date fields without a year* — rather than on the kind. -/
  | youngerThan1900RequiresYear
  deriving Repr, DecidableEq

/-- Complete declaration-owned policy needed by stored partial-Date consumers and before a resolved temporal value can be rendered and checked as a computed target. The model time zone remains a separate model-wide input. -/
structure TemporalTargetPolicy where
  /-- Exact already-admitted format source, including component order, separators, and quoting. -/
  format : String
  partialMode : TemporalPartialMode := .full
  youngerThan1900Check : Bool := false
  deriving Repr, DecidableEq

/-- Static incoherence in one declaration-owned DateRange format policy. A refused pair is classified by an absent source where one is missing and by unsupported pair membership otherwise; no external Kernel diagnostic class is claimed for either. -/
inductive DateRangeDeclarationPolicyError where
  | emptyFormat
  | emptySeparator
  | unsupportedPair
  deriving Repr, DecidableEq

/-- The declared reading of a yearless DateRange whose endpoints wrap the calendar year, named for the Kernel's `interpretationOfYear` tokens. `anchorStart` is `FROM` and `anchorFinish` is `TO`; each names the endpoint that stays in the Base Year. -/
inductive DateRangeYearInterpretation where
  | anchorStart
  | anchorFinish
  deriving Repr, DecidableEq

/-- Place the two calendar years of a wrapping yearless range. The anchored endpoint keeps the Base Year and the other endpoint moves into the adjacent year, so the completed range spans exactly one year boundary. -/
def DateRangeYearInterpretation.wrappingYears :
    DateRangeYearInterpretation → Int → Int × Int
  | .anchorStart, baseYear => (baseYear, baseYear + 1)
  | .anchorFinish, baseYear => (baseYear - 1, baseYear)

/-- Exact DateRange declaration sources retained separately from the decoded endpoint value. An absent `interpretationOfYear` is the standard reading, under which a wrapping yearless range is formally invalid; a present-but-empty declared token is illegal at model deserialization rather than defaulting, so it never reaches this record and has no representation here. The key is accepted on every admitted pair, so it takes no part in declaration admission. -/
structure DateRangeDeclarationPolicy where
  format : String
  separator : String
  interpretationOfYear : Option DateRangeYearInterpretation := none
  deriving Repr, DecidableEq

/-- Decide declaration admission against the exact Kernel-measured `(format, separator)` allowlist. Month-only is the sole format admitting the legal empty separator, and admission carries no claim that every DateRange operation supports the pair. -/
def DateRangeDeclarationPolicy.admitted
    (policy : DateRangeDeclarationPolicy) : Bool :=
  match policy.format, policy.separator with
  | "dd.MM.yyyy", "-" => true
  | "yyyy-MM-dd", "/" => true
  | "yyyy", "/" => true
  | "yyyy-MM", "/" => true
  | "MM", "/" => true
  | "MM-dd", "/" => true
  | "MM", "" => true
  | "dd.MM", "-" => true
  | _, _ => false

/-- Classify one already-refused declaration. An absent source keeps its own cause because it is refused under every format; any other refused pair is unsupported membership rather than a missing source. This is total on refused pairs only: admission is decided separately. -/
def DateRangeDeclarationPolicy.refusal
    (policy : DateRangeDeclarationPolicy) : DateRangeDeclarationPolicyError :=
  if policy.format.isEmpty then
    .emptyFormat
  else if policy.separator.isEmpty then
    .emptySeparator
  else
    .unsupportedPair

/-- Refuse every declaration outside the admitted allowlist, before raw DateRange parsing. -/
def DateRangeDeclarationPolicy.error?
    (policy : DateRangeDeclarationPolicy) :
    Option DateRangeDeclarationPolicyError :=
  if policy.admitted then none else some policy.refusal

/-- Exact DateRange presentations shared by bounded stored-input and computed-target consumers. The model-owned source format and separator remain in `DateRangeDeclarationPolicy`. -/
inductive DateRangeFormat where
  | isoSlash
  | dayMonthYearDash
  deriving Repr, DecidableEq

namespace DateRangeFormat

/-- Recognize only the two externally established declaration pairs used by the current checked input and target fragments. -/
def ofPolicy? (policy : DateRangeDeclarationPolicy) : Option DateRangeFormat :=
  if policy.format == "yyyy-MM-dd" && policy.separator == "/" then
    some .isoSlash
  else if policy.format == "dd.MM.yyyy" && policy.separator == "-" then
    some .dayMonthYearDash
  else
    none

/-- Exact separator carried by one admitted DateRange presentation. -/
def separator : DateRangeFormat → String
  | .isoSlash => "/"
  | .dayMonthYearDash => "-"

end DateRangeFormat

/-- Check only the cross-field invariants visible at the parser-independent flat boundary.

A non-full partial mode belongs to a full Date declaration. The opt-in pre-1900 check belongs to a
Date declaration **whose format carries a year**: the Kernel refuses a year-free one outright with
`MVK_ADDITIONAL_CHECK_INVALID`, and its message keys on the components rather than on the kind
([inbound](../../docs/SOURCES.md#inbound-2026-09-05c)). This arm admitted every year-free Date
declaration with the guard set, which is an **over**-admission — a legal-looking model the Kernel
rejects — and the opposite direction from the under-admissions the kind/format sweep was finding, so
that sweep could not have surfaced it. -/
def TemporalTargetPolicy.errorFor?
    (policy : TemporalTargetPolicy)
    (kind : TemporalKind) (components : TemporalComponents) :
    Option TemporalTargetPolicyError :=
  if policy.format.isEmpty then
    some .emptyFormat
  else
    match kind with
    | .date =>
        if policy.youngerThan1900Check && !components.year then
          some .youngerThan1900RequiresYear
        else if policy.partialMode == .full ||
            components == TemporalComponents.fullDate then
          none
        else
          some .partialModeRequiresFullDate
    | .time | .dateTime =>
        if policy.partialMode != .full then
          some .partialModeRequiresFullDate
        else if policy.youngerThan1900Check then
          some .youngerThan1900RequiresDate
        else
          none

/-- Equality and inequality, unlike directional comparisons, require both formats to agree on whether they expose a time component. -/
def TemporalComparisonOp.requiresSameTimePresence : TemporalComparisonOp → Bool
  | .equal | .notEqual => true
  | .before | .beforeOrEqual | .after | .afterOrEqual => false

/-- Year presence after optional Base-Year supplementation: the one rule the direct-comparison
gate and the temporal-operation operand gate genuinely share. It is factored rather than written
twice because it is the rule this family keeps getting wrong in prose — a declared Base Year makes
it **vacuous**, in both directions, which two separate accounts had stated unqualified. -/
def temporalYearPresenceAgrees (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  (left.withBaseYear hasBaseYear).year == (right.withBaseYear hasBaseYear).year

/-- Static admission for a direct temporal comparison. This intentionally does not require equal component sets. -/
def TemporalComparisonOp.admitsFormats (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (left right : TemporalComponents) : Bool :=
  temporalYearPresenceAgrees hasBaseYear left right &&
    (left.hasDate == right.hasDate) &&
    (!op.requiresSameTimePresence || (left.hasTime == right.hasTime))

/-- `Now` obeys ordinary direct-comparison compatibility and the additional generated-code restriction that the other operand expose a time component. -/
def TemporalComparisonOp.admitsNow (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (other : TemporalComponents) : Bool :=
  other.hasTime && op.admitsFormats hasBaseYear other TemporalComponents.now

/-- `Today` is admitted exactly as a complete date-shaped operand through the ordinary direct-comparison gate. -/
def TemporalComparisonOp.admitsToday (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (other : TemporalComponents) : Bool :=
  op.admitsFormats hasBaseYear other TemporalComponents.today

/-- Base Year is already known to exist here, so it supplies the year component while otherwise following the ordinary date-shaped format gate. -/
def TemporalComparisonOp.admitsBaseYear (op : TemporalComparisonOp)
    (other : TemporalComponents) : Bool :=
  other.hasDate && op.admitsFormats true other TemporalComponents.baseYear

/-- Static admission shared by temporal operand-list and field-list extrema: the original date class must agree and component sets must agree exactly after Base Year supplementation. -/
def temporalAggregateFormatsCompatible (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  (left.hasDate == right.hasDate) &&
    (left.withBaseYear hasBaseYear == right.withBaseYear hasBaseYear)

/-- The calendar or clock unit a two-operand temporal *operation* steps in, which decides
which single component each of its operands must resolve. This is a different gate from
the direct-comparison one above: a comparison never requires a particular component, only
agreement, while an operation cannot step in a unit its operand does not carry. -/
inductive TemporalOperationUnit where
  | days
  | months
  | years
  | hours
  | minutes
  | seconds
  deriving Repr, DecidableEq

namespace TemporalOperationUnit

/-- The one component an operand must expose to be steppable in this unit. -/
def requiredComponent : TemporalOperationUnit → (TemporalComponents → Bool)
  | .days => TemporalComponents.day
  | .months => TemporalComponents.month
  | .years => TemporalComponents.year
  | .hours => TemporalComponents.hour
  | .minutes => TemporalComponents.minute
  | .seconds => TemporalComponents.second

/-- Whether one operand resolves this unit, reading the **Base-Year-supplemented** components.
Supplementation genuinely feeds this gate rather than only the agreement one: a yearless pair
is refused in `years` with no Base Year and admitted once the model declares one. It supplies
the year alone, so a month-only operand stays unsteppable in `days` in a configured model. -/
def operandResolves (unit : TemporalOperationUnit) (hasBaseYear : Bool)
    (components : TemporalComponents) : Bool :=
  unit.requiredComponent (components.withBaseYear hasBaseYear)

/-- Why a temporal operation refuses an operand pair. The two grounds carry **different**
Kernel codes — `MVK_WRONG_DATE_FORMAT_FOR_OP` for granularity and
`MVK_DATE_WITH_AND_WITHOUT_YEAR` for year disagreement — and their order is measured rather
than chosen: a month-only operand beside a year-bearing constant disagrees about the year as
well, and the Kernel reports the granularity code. -/
inductive OperandFault where
  | granularity
  | yearDisagreement
  deriving Repr, DecidableEq

/-- Classify one operand pair, granularity first. `none` is admission. -/
def operandFault? (unit : TemporalOperationUnit) (hasBaseYear : Bool)
    (left right : TemporalComponents) : Option OperandFault :=
  if !(unit.operandResolves hasBaseYear left && unit.operandResolves hasBaseYear right) then
    some .granularity
  else if !temporalYearPresenceAgrees hasBaseYear left right then
    some .yearDisagreement
  else
    none

/-- Static admission for a two-operand temporal operation. -/
def admitsOperands (unit : TemporalOperationUnit) (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  (unit.operandFault? hasBaseYear left right).isNone

end TemporalOperationUnit

/-- A DATE declaration format that omits at least one component. -/
inductive OmittingDateFormat where
  /-- `yyyy` — the value is a whole calendar year. -/
  | year
  /-- `yyyy-MM` — the value is a whole calendar month. -/
  | yearMonthDashed
  /-- `yyyyMM` — the same value under a separator-free spelling, refused by the dashed format. -/
  | yearMonthConcatenated
  /-- `MM` — a yearless month, denoting no interval of concrete dates. -/
  | month
  /-- `MM-dd` — a yearless month and day, whose day is bounded by the month's greatest possible. -/
  | monthDay
  /-- `MMdd` — the same month-day value without a separator. -/
  | monthDayConcatenated
  /-- `ddMM` — the same yearless components in day-month order. -/
  | dayMonthConcatenated
  deriving Repr, DecidableEq

namespace OmittingDateFormat

/-- Admit the seven measured component-omitting formats. The three complete formats belong to the full-Date
classifier and are refused here. -/
def ofSource? : String → Option OmittingDateFormat
  | "yyyy" => some .year
  | "yyyy-MM" => some .yearMonthDashed
  | "yyyyMM" => some .yearMonthConcatenated
  | "MM" => some .month
  | "MM-dd" => some .monthDay
  | "MMdd" => some .monthDayConcatenated
  | "ddMM" => some .dayMonthConcatenated
  | _ => none

/-- Whether this format's value carries a year, and therefore denotes an interval of concrete dates. -/
def carriesYear : OmittingDateFormat → Bool
  | .year | .yearMonthDashed | .yearMonthConcatenated => true
  | .month | .monthDay | .monthDayConcatenated | .dayMonthConcatenated => false

/-- The component set a declaration of this format exposes.

Derived from the format rather than declared beside it, because the two cannot disagree: the stored text
is what carries the components, so a `yyyy` field exposing a day would describe a value it has no way to
store. Feeding this to `TemporalComparisonOp.admitsFormats` reproduces the measured comparison matrix
exactly — any two year-bearing formats compare regardless of how many components they carry, and a
yearless one is refused against a year-bearing one without a Base Year. -/
def components : OmittingDateFormat → TemporalComponents
  | .year =>
      { year := true, month := false, day := false
        hour := false, minute := false, second := false }
  | .yearMonthDashed | .yearMonthConcatenated =>
      { year := true, month := true, day := false
        hour := false, minute := false, second := false }
  | .month =>
      { year := false, month := true, day := false
        hour := false, minute := false, second := false }
  | .monthDay | .monthDayConcatenated | .dayMonthConcatenated =>
      { year := false, month := true, day := true
        hour := false, minute := false, second := false }

end OmittingDateFormat

end A12Kernel
