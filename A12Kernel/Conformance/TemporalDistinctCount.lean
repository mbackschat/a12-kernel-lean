import A12Kernel.Elaboration.TemporalDistinctCount

/-! # A12Kernel.Conformance.TemporalDistinctCount — the component-set gate, against its neighbour

`NumberOfDifferentValues` and `FieldValuesNotUnique` accept the same operand shapes and gate them
differently, so every row here is paired with the neighbour's answer on the identical list. That
pairing is the point: a gate that merely *looked* right on this operator would be indistinguishable
from the neighbour's until a pair separates them, and one such pair exists
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-distinct-count-component-set-and-locus),
nine `rule check` rows in one batch).

The fixture's component sets agree with each declaration's format, which is what any model this
project admits looks like; a declaration whose format and components contradict each other is
refused by the stored-text classifiers and its authorability is unmeasured.
-/

namespace A12Kernel.Conformance.TemporalDistinctCount

open A12Kernel

private def yearMonth : TemporalComponents :=
  { year := true, month := true, day := false
    hour := false, minute := false, second := false }

private def monthOnly : TemporalComponents :=
  { year := false, month := true, day := false
    hour := false, minute := false, second := false }

private def monthDay : TemporalComponents :=
  { year := false, month := true, day := true
    hour := false, minute := false, second := false }

private def clockOnly : TemporalComponents :=
  { year := false, month := false, day := false
    hour := true, minute := true, second := true }

private def instantSet : TemporalComponents :=
  { year := true, month := true, day := true
    hour := true, minute := true, second := true }

private def dayAndClock : TemporalComponents :=
  { year := false, month := false, day := true
    hour := true, minute := true, second := true }

private def noonHalf : TimeOfDay :=
  { hour := 12, minute := 30, second := 0, valid := by decide }

private def afternoonHalf : TimeOfDay :=
  { hour := 13, minute := 30, second := 0, valid := by decide }

private def dateField (id : FieldId) (name format : String)
    (components : TemporalComponents := TemporalComponents.fullDate) :
    FlatFieldDecl := {
  id
  groupPath := ["Probe"]
  name
  policy := { kind := .temporal .date components }
  temporalTargetPolicy := some { format }
}

/-- Two date-only groups at the root, differing in exactly what the two operators' gates read: one
    carries a single component set in two spellings, the other two component sets. -/
private def groupField (id : FieldId) (group name format : String)
    (components : TemporalComponents := TemporalComponents.fullDate) :
    FlatFieldDecl := {
  id
  groupPath := ["Probe", group]
  name
  policy := { kind := .temporal .date components }
  temporalTargetPolicy := some { format }
}

private def model : FlatModel := {
  fields := [
    dateField 1 "FiledOn" "yyyy-MM-dd",
    dateField 2 "ClosedOn" "dd.MM.yyyy",
    dateField 3 "CoverFrom" "yyyy-MM" yearMonth,
    -- A second root-level year-month field. Without it the component-omitting runtime case below
    -- could only pair `CoverFrom` with itself, which the duplicate gate refuses before the runtime
    -- restriction is reached — the case would pass without ever exercising it.
    dateField 20 "CoverTo" "yyyy-MM" yearMonth,
    -- A **partially known** declaration carrying the complete component set, so it differs from
    -- `FiledOn` in declared precision alone.
    { id := 21, groupPath := ["Probe"], name := "PartialDay"
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "dd.MM.yyyy", partialMode := .dayOptional } },
    { id := 22, groupPath := ["Probe"], name := "PartialDay2"
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "dd.MM.yyyy", partialMode := .dayOptional } },
    dateField 6 "SupersededFrom" "yyyy-MM-dd",
    { id := 4, groupPath := ["Probe"], name := "SkuText",
      policy := { kind := .string } },
    { id := 5, groupPath := ["Probe"], name := "Flag",
      policy := { kind := .boolean } },
    { id := 19, groupPath := ["Probe"], name := "Amount",
      policy := { kind := .number { scale := 0, signed := false } } },
    groupField 10 "MixBox" "IsoA" "yyyy-MM-dd",
    groupField 11 "MixBox" "DotB" "dd.MM.yyyy",
    groupField 12 "SetBox" "Full" "yyyy-MM-dd",
    groupField 13 "SetBox" "YearMonth" "yyyy-MM" yearMonth,
    { id := 14, groupPath := ["Probe", "TextBox"], name := "Note",
      policy := { kind := .string } },
    -- Two mixed expansions differing only in **declaration order**, which is what the class turns
    -- on. Nothing else about the pair varies.
    groupField 15 "DateFirstBox" "ADate" "yyyy-MM-dd",
    { id := 16, groupPath := ["Probe", "DateFirstBox"], name := "BNum",
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 17, groupPath := ["Probe", "NumFirstBox"], name := "ANum",
      policy := { kind := .number { scale := 0, signed := false } } },
    groupField 18 "NumFirstBox" "BDate" "yyyy-MM-dd",
    -- Yearless declarations, for the Base Year supplementation rows. Two `MM` fields, because a
    -- single one could only pair with itself and the duplicate gate answers first.
    dateField 23 "MonthOnly" "MM" monthOnly,
    dateField 24 "MonthOnly2" "MM" monthOnly,
    dateField 25 "MonthDay" "MM-dd" monthDay,
    -- A time-bearing pair, so the runtime restriction below has a reachable witness.
    { id := 26, groupPath := ["Probe"], name := "ClockA"
      policy := { kind := .temporal .time clockOnly }
      temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 27, groupPath := ["Probe"], name := "ClockB"
      policy := { kind := .temporal .time clockOnly }
      temporalTargetPolicy := some { format := "HH:mm:ss" } },
    -- A DATETIME declared the degenerate clock format, which is the cross-kind witness.
    { id := 28, groupPath := ["Probe"], name := "StampClock"
      policy := { kind := .temporal .dateTime clockOnly }
      temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 29, groupPath := ["Probe"], name := "Stamp1"
      policy := { kind := .temporal .dateTime instantSet }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
    { id := 30, groupPath := ["Probe"], name := "Stamp2"
      policy := { kind := .temporal .dateTime instantSet }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
    -- A time-bearing set naming only *some* date components. No admitted format spells one, so this
    -- pair exists to keep the runtime certificate reachable rather than hypothetical.
    { id := 31, groupPath := ["Probe"], name := "PartialStamp1"
      policy := { kind := .temporal .dateTime dayAndClock }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
    { id := 32, groupPath := ["Probe"], name := "PartialStamp2"
      policy := { kind := .temporal .dateTime dayAndClock }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }]
}

/-- The identical model with a Base Year declared. Every supplementation row below pairs against its
    own `model` control, so the verdict attaches to the Base Year and not to the fixture. -/
private def baseYearModel : FlatModel := { model with baseYear := some 2024 }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def pair (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

/-- Whether one authored pair elaborates against an arbitrary model, so a row can vary the model's
    Base Year while holding the pair fixed. -/
private def admits (candidate : FlatModel) (first second : String) : Bool :=
  (elaborateTemporalDistinctCountSource candidate ["Probe"] (pair first second)).toOption.isSome

/-- This operator's verdict on one authored pair. -/
private def distinct? (first second : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalDistinctCountSource model ["Probe"] (pair first second) with
  | .ok _ => none
  | .error error => error.diagnostic?

private def distinctAdmitted (first second : String) : Bool :=
  (elaborateTemporalDistinctCountSource model ["Probe"] (pair first second)).toOption.isSome

/-- The neighbouring operator's verdict on the identical list. -/
private def unique? (first second : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalValuesNotUniqueSource model ["Probe"] (pair first second) with
  | .ok _ => none
  | .error error => error.diagnostic?

/- **The separating pair, and the reason this operator needs its own gate at all.** Two DATE fields
   naming the same components in different spellings are admitted here and refused by the neighbour.
   Adopting the neighbour's format-equality gate would have over-rejected this row — the inverse of
   the over-admission this project usually guards against, and the reason a measured neighbour is
   not a licence. -/
example :
    distinctAdmitted "FiledOn" "ClosedOn" = true ∧
      unique? "FiledOn" "ClosedOn" = some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- **A differing component set is refused, which is what keeps the gate from being vacuous.** The
   admitted row above and this one differ only in the second operand's component set, so a gate that
   admitted everything would satisfy the first and fail here. The Kernel's message names both
   formats rather than the sets, which is why the error carries formats. -/
/- **A declared Base Year supplements YEAR into every operand's set before they are compared, and
   the gate stays exact after that.** Measured on this operator: at `baseYear: "2024"` a yearless
   `MM` operand is admitted beside `yyyy-MM` and `MM-dd` beside a complete date, while `MM-dd`
   beside `yyyy-MM` is still refused because the remaining components disagree
   ([checkpoint](../../docs/SOURCES.md#src-distinct-count-component-omitting-fold)). The last two
   rows are the controls that make this the Base Year's doing: the same mixed pair is refused when
   no Base Year is declared, and a same-set yearless pair is admitted without one. -/
example :
    (admits baseYearModel "MonthOnly" "CoverFrom",
      admits baseYearModel "MonthDay" "FiledOn",
      admits baseYearModel "MonthDay" "CoverFrom",
      admits model "MonthOnly" "CoverFrom",
      admits model "MonthOnly" "MonthOnly2") =
      (true, true, false, false, true) := by
  native_decide

/- **A list whose declared sets differ under supplementation has an evaluator, in either operand
   order.** A complete date beside a supplemented `MM-dd` is admitted, and each operand is projected
   through its *own* declared set, so the Base Year supplies exactly the component the yearless
   operand lacks. The order rows matter because the arm is read from the leading operand: it must
   answer the same either way. -/
example :
    ((match (elaborateTemporalDistinctCountSource baseYearModel ["Probe"]
        (pair "FiledOn" "MonthDay")).toOption with
      | some source => (checkTemporalDistinctCountRun source).toOption.isSome
      | none => false),
      (match (elaborateTemporalDistinctCountSource baseYearModel ["Probe"]
        (pair "MonthDay" "FiledOn")).toOption with
      | some source => (checkTemporalDistinctCountRun source).toOption.isSome
      | none => false),
      (match (elaborateTemporalDistinctCountSource baseYearModel ["Probe"]
        (pair "FiledOn" "ClosedOn")).toOption with
      | some source => (checkTemporalDistinctCountRun source).toOption.isSome
      | none => false)) =
      (true, true, true) := by
  native_decide

example : distinct? "FiledOn" "CoverFrom" = some .dateFormatsNotCompatible := by
  native_decide

/- **Date-first with a non-temporal member draws the cross-family class**, not the component-set one:
   the kind gate runs before the list's own gate, so an operand that is not temporal at all never
   reaches the component comparison. -/
example : distinct? "FiledOn" "SkuText" = some .dateAndNonDate := by
  native_decide

/- **The kind-domain code is this operator's, one token from the neighbour's.** A Boolean draws
   `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED` here and the `CMP_`-less form there, on the same
   list. The two codes name different operators' gates and neither may be read off the other; this
   row exists because the names invite exactly that carry-over. -/
example :
    distinct? "Flag" "FiledOn" = some .onlyStringEnumNumberCmpDateAllowed ∧
      unique? "Flag" "FiledOn" = some .onlyStringEnumNumberDateAllowed ∧
      KernelStaticDiagnostic.onlyStringEnumNumberCmpDateAllowed.kernelCode
        = "MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED" ∧
      KernelStaticDiagnostic.onlyStringEnumNumberDateAllowed.kernelCode
        = "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED" := by
  native_decide

/- **Two distinct fields sharing one format are admitted by both operators**, which is what fixes
   the separation above as being about the *spelling* rather than about carrying two operands. It is
   also the row that dissolves the neighbour's refusal: its code names kinds, but the gate is the
   format string, and holding the format fixed while varying nothing else shows it. -/
example :
    distinctAdmitted "FiledOn" "SupersededFrom" = true ∧
      unique? "FiledOn" "SupersededFrom" = none := by
  native_decide


/-! ## A group operand, gated by **this** operator's rule

The group is admitted, and its expansion meets the component-set gate rather than the neighbour's
format-equality one. The pair below is the whole point: one group, two operators, two verdicts
([checkpoint](../../docs/SOURCES.md#src-temporal-group-operand-follows-its-own-operator)). Reusing
the neighbour's group certificate — the tempting move, since it already exists and already certifies
temporal group expansions — would have refused the admitted half. -/
private def groupOperand (group : String) : SurfaceFieldEntitySource :=
  { first := .group (.path { base := .absolute, groups := ["Probe", group] })
    rest := [] }

private def distinctGroup? (group : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalDistinctCountSource model ["Probe"] (groupOperand group) with
  | .ok _ => none
  | .error error => error.diagnostic?

private def uniqueGroup? (group : String) : Option KernelStaticDiagnostic :=
  match elaborateTemporalValuesNotUniqueSource model ["Probe"]
      (groupOperand group) with
  | .ok _ => none
  | .error error => error.diagnostic?

/- One component set in two spellings: admitted here, refused by the neighbour. -/
example :
    (elaborateTemporalDistinctCountSource model ["Probe"]
      (groupOperand "MixBox")).toOption.isSome = true ∧
      uniqueGroup? "MixBox" = some .onlyStringEnumNumberDateAllowed := by
  native_decide

/- Two component sets: refused here, with this operator's own class. Without this row the admission
   above is equally well explained by the group slot skipping the gate entirely — which is the
   failure mode that would let a group smuggle an incompatible declaration past it. -/
example : distinctGroup? "SetBox" = some .dateFormatsNotCompatible := by
  native_decide

/- The group's component set reaches the **list** gate too, so a group and a scalar operand are
   compared against each other rather than each being checked alone. -/
example :
    (elaborateTemporalDistinctCountSource model ["Probe"]
      { first := .group (.path { base := .absolute, groups := ["Probe", "MixBox"] })
        rest := [.field (bare "CoverFrom")] }).toOption.isNone = true := by
  native_decide

/- A **non-temporal** declaration in the expansion is refused by both operators, and the refusal
   names that declaration's own path and kind rather than the group path with a fabricated one —
   which is why the offending declaration is found and re-certified rather than reported
   positionally. The duplicated certificate covers the component gate only; this arm is delegated,
   so the two operators cannot disagree about *whether* such a group is refused.

   `TextBox`'s expansion leads with the String, so this operator claims **no class** — the list is
   another overload's, exactly as a scalar list led by a non-temporal operand is. The rows below
   separate that from a merely mixed expansion. -/
example :
    (elaborateTemporalDistinctCountSource model ["Probe"]
      (groupOperand "TextBox")).toOption.isNone = true ∧
      (elaborateTemporalValuesNotUniqueSource model ["Probe"]
        (groupOperand "TextBox")).toOption.isNone = true ∧
      distinctGroup? "TextBox" = none := by
  native_decide

/-! ### Declaration order decides the class, in a group's expansion as in a scalar list

The same two kinds in the other order draw a different code, and the scalar controls agree cell for
cell ([checkpoint](../../docs/SOURCES.md#src-temporal-group-operand-follows-its-own-operator)). So
the first-operand rule reaches a group's expansion rather than stopping at the authored slots, and a
projection keyed on the *offending* kind alone would be right in one order and wrong in the other —
which is exactly what this operator shipped before the pair was measured. -/
example :
    distinctGroup? "DateFirstBox" = some .dateAndNonDate ∧
      distinct? "FiledOn" "Amount" = some .dateAndNonDate := by
  native_decide

/- A leading **Number** makes the list the other overload's, so this one refuses claiming no class
   rather than reporting the date code. The Kernel's own answer there is
   `MVK_NUMBER_AND_NON_NUMBER`, which that overload owns. -/
example :
    distinctGroup? "NumFirstBox" = none ∧
      (elaborateTemporalDistinctCountSource model ["Probe"]
        (groupOperand "NumFirstBox")).toOption.isNone = true := by
  native_decide

/-! ## The runtime fold, and the identity that separates it from its neighbour

`spec/07` states that these two operators compare **different things** over the same entity lists:
`FieldValuesNotUnique` compares the exact stored text, this one the decoded date. The pair of cases
below is the mirror of the separator in that operator's own module — the same two cells, holding one
decoded date under two distinct stored texts, are *not* a duplicate there and *are* one value here.
Either case alone is consistent with both accounts; together they pin the contrast the clause makes.
-/

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (year month day : Nat) : TemporalValue :=
  .date {
    instant := { epochMillis := 0 }
    parts := { year := (year : Int), month, day }
    basis := .storedGregorian }

/-- One placed temporal cell whose stored text and decoded value are supplied independently, so a
    case can hold the decoded value fixed while varying the text. -/
private def temporalCell (field : FieldId) (stored : String)
    (value : TemporalValue) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw := .parsed (.temporal value) }

private def count? (first second : String) (cells : List ClassifiedCellInput) :
    Option NumericOperand := do
  let source ←
    (elaborateTemporalDistinctCountSource model ["Probe"] (pair first second)).toOption
  let run ← (checkTemporalDistinctCountRun source).toOption
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption
  (run.evaluate document []).toOption

/- **The compared identity is the decoded date.** One date under two distinct stored texts counts
   once; two dates count twice. The first row is the one a stored-text account gets wrong, and it is
   the exact pair the uniqueness operator's own module locks as a non-duplicate. -/
example :
    count? "FiledOn" "ClosedOn"
        [temporalCell 1 "2024-03-05" (dateValue 2024 3 5),
          temporalCell 2 "05.03.2024" (dateValue 2024 3 5)] =
      some (.value 1 .fixed) ∧
    count? "FiledOn" "ClosedOn"
        [temporalCell 1 "2024-03-05" (dateValue 2024 3 5),
          temporalCell 2 "06.03.2024" (dateValue 2024 3 6)] =
      some (.value 2 .fixed) := by
  native_decide

/- An absent cell does not contribute a value and leaves the count able to grow, which is the shared
   aggregate's rule reaching this carrier rather than a second one. -/
example :
    count? "FiledOn" "ClosedOn"
        [temporalCell 1 "2024-03-05" (dateValue 2024 3 5)] =
      some (.value 1 .growOnly) := by
  native_decide

/- **A component-omitting list folds at its own precision, and the omitted day is discarded rather
   than trusted.** Both operands are `yyyy-MM` and the two cells carry the same year and month with
   *different* days — which a producer is free to do, because the document's coherence check
   re-derives boolean, confirm and DateRange values from their stored text but not temporal ones. The
   count is 1, so the identity is the declared set's; a fold that carried the cell's day through
   would answer 2 and would make the count depend on the producer rather than the model. The second
   row moves the month and answers 2, so the first is not a collapse of everything. -/
example :
    count? "CoverFrom" "CoverTo"
        [temporalCell 3 "2024-03" (dateValue 2024 3 1),
          temporalCell 20 "2024-03" (dateValue 2024 3 17)] =
      some (.value 1 .fixed) ∧
    count? "CoverFrom" "CoverTo"
        [temporalCell 3 "2024-03" (dateValue 2024 3 1),
          temporalCell 20 "2024-04" (dateValue 2024 4 1)] =
      some (.value 2 .fixed) := by
  native_decide

/- **A yearless list with no Base Year folds on the calendar position it spells.** `MM` carries
   neither year nor day, so both are discarded and two cells differing in either still count once;
   moving the month answers 2. This is the arm that must not be a date completed against an invented
   year — the two cells below carry *different* supplied years, and the count is still 1. -/
example :
    count? "MonthOnly" "MonthOnly2"
        [temporalCell 23 "03" (dateValue 2024 3 9),
          temporalCell 24 "03" (dateValue 1999 3 25)] =
      some (.value 1 .fixed) ∧
    count? "MonthOnly" "MonthOnly2"
        [temporalCell 23 "03" (dateValue 2024 3 1),
          temporalCell 24 "04" (dateValue 2024 4 1)] =
      some (.value 2 .fixed) := by
  native_decide

/- **A clock list folds on the decoded reading, and a TIME agrees with a DATETIME declared the
   degenerate `HH:mm:ss`.** The cross-kind row is the one that fixes the arm: the identity follows
   the declared component set and not the declared kind, so both operands must land in the same arm
   ([checkpoint](../../docs/SOURCES.md#src-distinct-count-time-bearing-fold)). The two cells carry
   *different* transport instants for one clock reading, which is what a kind-keyed or
   instant-keyed identity would answer 2 to. -/
example :
    count? "ClockA" "ClockB"
        [temporalCell 26 "12:30:00" (.time { epochMillis := 0 } noonHalf),
          temporalCell 27 "12:30:00" (.time { epochMillis := 86400000 } noonHalf)] =
      some (.value 1 .fixed) ∧
    count? "ClockA" "StampClock"
        [temporalCell 26 "12:30:00" (.time { epochMillis := 0 } noonHalf),
          -- A DATETIME declared the degenerate clock format holds a **`.time`** value: the cell's
          -- value shape follows the declared component set, and `formalCheck` marks a `.dateTime`
          -- value under this declaration malformed. That is what makes the cross-kind identity fall
          -- out of the representation instead of needing a case of its own.
          temporalCell 28 "12:30:00" (.time { epochMillis := 3600000 } noonHalf)] =
      some (.value 1 .fixed) ∧
    count? "ClockA" "ClockB"
        [temporalCell 26 "12:30:00" (.time { epochMillis := 0 } noonHalf),
          temporalCell 27 "13:30:00" (.time { epochMillis := 0 } afternoonHalf)] =
      some (.value 2 .fixed) := by
  native_decide

/- **The one runtime certificate left is a time-bearing set naming only some of its atom's
   components.** `TimeOfDay` and `Instant` carry every component they have, so unlike the date arms
   there is nothing to mask a partial set down to; the fold would otherwise answer at a precision the
   declaration does not name. The admitted control beside it is the complete instant pair below. -/
example :
    (match (elaborateTemporalDistinctCountSource model ["Probe"]
        (pair "PartialStamp1" "PartialStamp2")).toOption with
      | some source =>
          match checkTemporalDistinctCountRun source with
          | .error (.incompleteTimeBearingSet components) => components == dayAndClock
          | _ => false
      | none => false) = true := by
  native_decide

/- **An instant list folds on the exact moment.** This arm holds the instant rather than the decoded
   label because the two are not separable by stored text within one model zone, and the arm says so
   rather than claiming the question settled; the pair below differs in the instant alone. -/
example :
    count? "Stamp1" "Stamp2"
        [temporalCell 29 "2024-03-05T12:30:00"
            (.dateTime { epochMillis := 1709641800000 }
              { year := 2024, month := 3, day := 5 } noonHalf .storedGregorian),
          temporalCell 30 "2024-03-05T12:30:00"
            (.dateTime { epochMillis := 1709641800000 }
              { year := 2024, month := 3, day := 5 } noonHalf .storedGregorian)] =
      some (.value 1 .fixed) ∧
    count? "Stamp1" "Stamp2"
        [temporalCell 29 "2024-03-05T12:30:00"
            (.dateTime { epochMillis := 1709641800000 }
              { year := 2024, month := 3, day := 5 } noonHalf .storedGregorian),
          temporalCell 30 "2024-03-05T13:30:00"
            (.dateTime { epochMillis := 1709645400000 }
              { year := 2024, month := 3, day := 5 } afternoonHalf .storedGregorian)] =
      some (.value 2 .fixed) := by
  native_decide

/- The group restriction is the other one, and it is reachable rather than hypothetical: `MixBox` is
   a group expansion this operator **admits statically**, locked above, and it still has no evaluator
   because no retained row measures a group expansion's runtime here. -/
example :
    (match (elaborateTemporalDistinctCountSource model ["Probe"]
        (groupOperand "MixBox")).toOption with
      | some source =>
          match checkTemporalDistinctCountRun source with
          | .error .groupOperand => true
          | _ => false
      | none => false) = true := by
  native_decide

/- And the complete-date pair the same gate admits, which keeps the rows above from reading as "this
   runtime refuses everything". -/
example :
    (match (elaborateTemporalDistinctCountSource model ["Probe"]
        (pair "FiledOn" "ClosedOn")).toOption with
      | some source => (checkTemporalDistinctCountRun source).toOption.isSome
      | none => false) = true := by
  native_decide

/- **The two neighbouring operators split on declared precision, and in the opposite direction from
   their comparability rule.** A partially known Date is refused here — it has no decoded date to
   compare — and admitted by `FieldValuesNotUnique`, which compares the exact stored text a partial
   does have ([checkpoint](../../docs/SOURCES.md#src-partial-date-precision-operand-gate)). The
   admitted full-precision pair beside it is what makes this a precision gate rather than a refusal
   of the fixture, and the uniqueness row is what makes it an asymmetry rather than a shared rule. -/
example :
    ((match elaborateTemporalDistinctCountSource model ["Probe"]
        (pair "PartialDay" "FiledOn") with
      | .error error => error.diagnostic?
      | .ok _ => none),
      (elaborateTemporalValuesNotUniqueSource model ["Probe"]
        (pair "PartialDay" "PartialDay2")).toOption.isSome,
      (elaborateTemporalDistinctCountSource model ["Probe"]
        (pair "FiledOn" "ClosedOn")).toOption.isSome) =
    (some .partialDateNotAllowed, true, true) := by
  native_decide

end A12Kernel.Conformance.TemporalDistinctCount
