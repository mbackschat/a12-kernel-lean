import A12Kernel.Elaboration.TemporalExtremumStream

/-! # A12Kernel.Conformance.TemporalExtremumReducedPrecision — the extrema over a component-omitting list

The Kernel admits and **orders** a component-omitting temporal list at the shared set's own
precision, the yearless case even with no Base Year declared, and the reversed document fires
nothing ([checkpoint](../../docs/SOURCES.md#src-extrema-component-omitting-fold)). These rows lock
both arms, which arm a given list takes, and — the part a happy-path row would leave standing — that
the components the declaration does not name are **discarded** rather than ordered on.

The section that decides what the fold *compares* is the mixed-precision one at the end. A
uniformly yearless list cannot settle it, because one declared Base Year shifts every operand
together; a yearless declaration beside a year-bearing one carries two different years inside a
single shared set and does settle it.

This module carries its own four-field model rather than the complete-precision slice's twenty-field
one, so each family's fixtures stay with that family and a reader of these rows sees only the
declarations they turn on.
-/

namespace A12Kernel.Conformance.TemporalExtremumReducedPrecision

open A12Kernel

private def dateField (id : Nat) (name : String)
    (components : TemporalComponents) (format : String) : FlatFieldDecl :=
  { id, groupPath := ["Probe"], name,
    policy := { kind := .temporal .date components },
    temporalTargetPolicy := some { format } }

/-- Year and month only: a component-omitting format that still carries a year. -/
private def yearMonth : TemporalComponents where
  year := true
  month := true
  day := false
  hour := false
  minute := false
  second := false

/-- Month only: a yearless component-omitting format. -/
private def monthOnly : TemporalComponents where
  year := false
  month := true
  day := false
  hour := false
  minute := false
  second := false

private def probeModel : FlatModel :=
  { fields := [
      dateField 4 "Month" yearMonth "yyyy-MM",
      dateField 5 "Month2" yearMonth "yyyy-MM",
      dateField 21 "MOnly" monthOnly "MM",
      dateField 22 "MOnly2" monthOnly "MM"] }

private def baseYearModel : FlatModel :=
  { probeModel with baseYear := some 2024 }

example : probeModel.validate.isOk = true ∧ baseYearModel.validate.isOk = true := by
  native_decide

private def fieldOperand (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups := ["Probe"], field := name }

private def sourceOf : List SurfaceFieldEntityOperand → SurfaceFieldEntitySource
  | [] => { first := fieldOperand "Month", rest := [] }
  | first :: rest => { first, rest }

private def admittedIn? (model : FlatModel) (names : List String) :
    Option (CheckedTemporalExtremumOperands model) :=
  (TemporalExtremumOperands.elaborate model ["Probe"]
    (sourceOf (names.map fieldOperand))).toOption

/-- The exact instant is irrelevant to this fold, which orders the decoded parts; it is fixed so a
    row cannot pass by accident of the epoch value. -/
private def dateValue (year month day : Nat) : DateValue where
  instant := { epochMillis := 0 }
  parts := { year, month, day }
  basis := .storedGregorian

private def dateCell (year month day : Nat) : RawCell :=
  .parsed (.temporal (.date (dateValue year month day)))

/-- Field ids read their own entry; anything unlisted is absent. -/
private def raw (cells : List (FieldId × RawCell)) : RawFlatContext where
  read id :=
    match cells.find? fun entry => entry.1 == id with
    | some entry => entry.2
    | none => .empty

private def ymd (year month day : Nat) : Option FullDate :=
  FullDate.ofYmd? year month day

private def maskedFoldIn? (model : FlatModel) (names : List String)
    (op : TemporalExtremumOp) (baseYear : Option Int)
    (cells : List (FieldId × RawCell)) :
    Option (SimpleComparisonOperand FullDate) := do
  let checked ← admittedIn? model names
  (TemporalExtremumStream.evalMaskedDate checked op baseYear
    (model.checkContext (raw cells)) .validation).toOption

private def yearlessFoldIn? (model : FlatModel) (names : List String)
    (op : TemporalExtremumOp) (cells : List (FieldId × RawCell)) :
    Option (SimpleComparisonOperand MonthDayValue) := do
  let checked ← admittedIn? model names
  (TemporalExtremumStream.evalYearlessDate checked op
    (model.checkContext (raw cells)) .validation).toOption

/-! ## Both arms, at the precision their declarations spell -/

/- **A year-bearing component-omitting list orders at its own precision.** Both operands are
   `yyyy-MM`; the earlier month wins under `minimum` and the later under `maximum`, each landing on
   the set's canonical day. -/
example :
    (maskedFoldIn? probeModel ["Month", "Month2"] .minimum none
        [(4, dateCell 2024 3 9), (5, dateCell 2024 4 2)],
      maskedFoldIn? probeModel ["Month", "Month2"] .maximum none
        [(4, dateCell 2024 3 9), (5, dateCell 2024 4 2)]) =
      ((ymd 2024 3 1).map (fun date => .value date true),
        (ymd 2024 4 1).map (fun date => .value date true)) := by
  native_decide

/- **A robustness lock on this project's own carrier, claiming nothing about the Kernel.** Lean's
   `RawCell` retains a parsed `DateValue` beside the stored text and does not re-derive one from the
   other, so a `yyyy-MM` declaration can hold a cell whose day component is set. These two cells
   name one month and *different* days, and both extrema answer the identical masked value, which
   locks the fold's answer as independent of a component the declaration does not name; ordering on
   the cell's day would make `maximum` answer the 17th. Whether a Kernel document can carry that day
   under such a declaration is a reachability question, not measured — the ordering rows above are
   measured on distinct months ([checkpoint](../../docs/SOURCES.md#src-extrema-component-omitting-fold)). -/
example :
    (maskedFoldIn? probeModel ["Month", "Month2"] .maximum none
        [(4, dateCell 2024 3 1), (5, dateCell 2024 3 17)],
      maskedFoldIn? probeModel ["Month", "Month2"] .minimum none
        [(4, dateCell 2024 3 1), (5, dateCell 2024 3 17)]) =
      ((ymd 2024 3 1).map (fun date => .value date true),
        (ymd 2024 3 1).map (fun date => .value date true)) := by
  native_decide

/- **A yearless list orders on the position it spells, with no Base Year.** The two cells carry
   *different* years, and the fold answers on the month alone — completing them against either
   year would order them by that completion. -/
example :
    (yearlessFoldIn? probeModel ["MOnly", "MOnly2"] .minimum
        [(21, dateCell 2024 3 9), (22, dateCell 1999 4 2)],
      yearlessFoldIn? probeModel ["MOnly", "MOnly2"] .maximum
        [(21, dateCell 2024 3 9), (22, dateCell 1999 4 2)]) =
      (some (.value { month := 3, day := 1 } true),
        some (.value { month := 4, day := 1 } true)) := by
  native_decide

/-! ## Which arm a list orders at

The selector reads the **certificate's** set, which the admission gate has already supplemented, so
these rows also lock that the supplementation is not applied twice.
-/

private def armOf (model : FlatModel) (names : List String) :
    Option TemporalExtremumStream.OmittingDateExtremumArm :=
  (admittedIn? model names).map TemporalExtremumStream.omittingDateExtremumArm

/- A year-bearing set orders as a date and a yearless one as a calendar position, both measured
   ([checkpoint](../../docs/SOURCES.md#src-extrema-component-omitting-fold)). -/
example :
    (armOf probeModel ["Month", "Month2"], armOf probeModel ["MOnly", "MOnly2"]) =
      (some .dated, some .yearless) := by
  native_decide

/- **A declared Base Year moves the yearless list to the dated arm**, which stays an internal
   consistency lock: the admission gate applies `withBaseYear` to every declaration before fixing
   the expected set — measured on *that* gate ([cases](TemporalExtremumOperands.lean)) — and the
   selector must agree with the certificate it reads rather than re-deriving the supplementation.

   The extrema's *ordering* under a declared Base Year is measured and it works, on both codegen
   strategies with the reversed document firing nothing
   ([checkpoint](../../docs/SOURCES.md#src-yearless-extrema-base-year-ordering)). That row alone
   cannot settle which value the fold compares, because one Base Year shifts a uniformly yearless
   list together. **A mixed-precision list can, and does — see the next section.** An earlier
   reading called `.dated` an unforced choice and argued no document could force it; that argument
   turned on every operand sharing one supplementation, which a yearless declaration beside a
   year-bearing one does not. -/
example : armOf baseYearModel ["MOnly", "MOnly2"] = some .dated := by native_decide

/-! ## The mixed-precision list, which is what says whether the year is compared -/

/- A yearless declaration beside a year-bearing one is **one shared set** once the gate has
   supplemented it, so the mixed list is admitted rather than refused for differing precision. -/
example : (admittedIn? baseYearModel ["MOnly", "Month"]).isSome = true := by
  native_decide

/- **The mixed-precision list forces the arm the section above could only assume.** Both
   declarations reach one shared set, and *within* it the two operands still carry different years —
   the yearless one the declared Base Year 2024, the other its own stored year. Both name March, so
   a fold discarding the year would answer one value for both extrema. It does not: the 2023 operand
   is the minimum, and moving it to 2025 moves both answers with it, which no year-discarding
   account produces. The Kernel's own row is the same one — a yearless operand beside a year-bearing
   one counts as **two** values and the extremum puts the earlier year first, supplemented by the
   declared Base Year and not by the sibling's year — accepted at the
   [component-omitting fold entry](../../docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-06-10). -/
example :
    (maskedFoldIn? baseYearModel ["MOnly", "Month"] .minimum (some 2024)
        [(21, dateCell 2024 3 9), (4, dateCell 2023 3 1)],
      maskedFoldIn? baseYearModel ["MOnly", "Month"] .maximum (some 2024)
        [(21, dateCell 2024 3 9), (4, dateCell 2023 3 1)],
      maskedFoldIn? baseYearModel ["MOnly", "Month"] .minimum (some 2024)
        [(21, dateCell 2024 3 9), (4, dateCell 2025 3 1)],
      maskedFoldIn? baseYearModel ["MOnly", "Month"] .maximum (some 2024)
        [(21, dateCell 2024 3 9), (4, dateCell 2025 3 1)]) =
      ((ymd 2023 3 1).map (fun date => .value date true),
        (ymd 2024 3 1).map (fun date => .value date true),
        (ymd 2024 3 1).map (fun date => .value date true),
        (ymd 2025 3 1).map (fun date => .value date true)) := by
  native_decide

/- **Where that year comes from, stated because the rows above do not pin it.** The masking
   projection is applied with the list's *shared* set, and the gate has already supplemented that
   set, so it reports the year as named and the projection then reads each cell's own year — the
   yearless-declared operand's included. On a coherently decoded document the two coincide, because
   a yearless declaration's stored text is itself decoded under the declared Base Year, which is why
   every row above agrees with the Kernel. A cell disagreeing with the Base Year under such a
   declaration orders on the cell's year instead, as this row shows; that is the same unmeasured
   reachability question the day-masking lock records, and it is left as an
   [SG23](../../docs/SEMANTICS-GAPS.md#sg23--the-temporal-extrema-operand-gate-element-type-and-fold)
   row rather than answered by narrowing a total function. Locked so the asymmetry with the masked
   day cannot be mistaken for the day rule. -/
example :
    maskedFoldIn? baseYearModel ["MOnly", "MOnly2"] .minimum (some 2024)
        [(21, dateCell 1999 3 9), (22, dateCell 2024 3 1)] =
      (ymd 1999 3 1).map (fun date => .value date true) := by
  native_decide

end A12Kernel.Conformance.TemporalExtremumReducedPrecision
