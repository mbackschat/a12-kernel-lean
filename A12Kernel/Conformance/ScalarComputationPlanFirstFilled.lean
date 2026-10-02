import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Authored scalar plan locks: `FirstFilledValue` at a join

Per kind `X`, `XA = FirstFilledValue(X1, X2)` feeds `XF = FirstFilledValue(XA, X3)`, read by two Number
guards `KX = 1` under `FieldFilled(XF)` and `KNX = 1` under `FieldNotFilled(XF)`, every reader authored
ahead of what it reads, over a Boolean, a `yyyy-MM` DateFragment, a Time, a DateTime, a full Date, a
DateRange and an Enumeration in one root `Fj`. The fixture is the model of the
[`FirstFilledValue` join checkpoint](../../docs/sources/computation-scheduling-probes.md#src-first-filled-join),
and every document row is the Kernel's, measured on both codegen strategies. A fragment cell is the
earliest date its stored month denotes, as the Kernel decodes it, and a completed fragment target is
read back the same way with its own rendering beside it.

`XA` and `XF` are seeded with a value no row computes, except the Boolean `BF`, left unseeded so a
computed `false` differs from its seed, and both guards are seeded `99`. A row projects every target to
its value, or `-` where the Kernel clears or writes nothing.

The rows separate a fresh read of `XA` from its seed (`r1`), a cleared `XA` that `XF` falls through from
one it would read as poison (`r2`), a poisoned `XA` that ends `XF`'s scan and poisons both guards from
one read as empty (`r3`), exhaustion from poison at the guards (`r4`), and a malformed third source the
scan never reaches (`r5`).
-/

namespace A12Kernel.Conformance.ScalarComputationPlanFirstFilled

open A12Kernel

/-- The six joined kinds, in the grid's order. -/
private inductive Kind where
  | boolean | fragment | time | dateTime | date | dateRange | enumeration
  deriving DecidableEq

private def Kind.all : List Kind :=
  [.boolean, .fragment, .time, .dateTime, .date, .dateRange, .enumeration]

private def Kind.letter : Kind → String
  | .boolean => "B" | .fragment => "G" | .time => "T" | .dateTime => "M" | .date => "D" | .dateRange => "R"
  | .enumeration => "E"

private def Kind.index : Kind → Nat
  | .boolean => 0 | .time => 1 | .dateTime => 2 | .date => 3 | .dateRange => 4 | .enumeration => 5
  | .fragment => 6

/-- The kind's seven fields, `X1`, `X2`, `X3`, `XA`, `XF`, `KX`, `KNX`, in that order. -/
private def Kind.names (kind : Kind) : List String :=
  ["1", "2", "3", "A", "F"].map (kind.letter ++ ·) ++ ["K" ++ kind.letter, "KN" ++ kind.letter]

private def Kind.id (kind : Kind) (slot : Nat) : FieldId := kind.index * 7 + slot

private def rangePolicy : DateRangeDeclarationPolicy := { format := "yyyy-MM-dd", separator := "/" }

private def Kind.declaration (kind : Kind) (slot : Nat) (name : String) : FlatFieldDecl :=
  let base : FlatFieldDecl := { id := kind.id slot, groupPath := ["Fj"], name, policy := { kind := .boolean } }
  if 5 ≤ slot then { base with policy := { kind := .number { scale := 0, signed := true } } }
  else match kind with
    | .boolean => base
    | .fragment => { base with
        policy := { kind := .temporal .date TemporalComponents.fullDate }
        temporalTargetPolicy := some { format := "yyyy-MM", partialMode := .yearOptional } }
    | .time => { base with
        policy := { kind := .temporal .time TemporalComponents.time }
        temporalTargetPolicy := some { format := "HH:mm:ss" } }
    | .dateTime => { base with
        policy := { kind := .temporal .dateTime TemporalComponents.now }
        temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full } }
    | .date => { base with
        policy := { kind := .temporal .date TemporalComponents.fullDate }
        temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }
    | .dateRange => { base with policy := { kind := .dateRange }, dateRangePolicy := some rangePolicy }
    | .enumeration => { base with
        policy := { kind := .enumeration }, enumeration := some { storedTokens := ["1", "2", "3"] } }

private def model : FlatModel :=
  { fields := Kind.all.flatMap fun kind =>
      (kind.names.zip (List.range 7)).map fun (name, slot) => kind.declaration slot name
    timeZoneId := "Europe/Berlin" }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def entities (first second : String) : SurfaceFieldEntitySource :=
  { first := .field (bare first), rest := [.field (bare second)] }

/-- The kind's `FirstFilledValue(first, second)` into `target`, as a plan step. -/
private def Kind.firstFilled? (kind : Kind) (target : FieldId) (first second : String) :
    Option (CheckedScalarComputationStep model) :=
  let list : SurfaceFirstFilledSource := .list (entities first second)
  (match kind with
    | .boolean => (checkBooleanFirstFilledComputation model ["Fj"] target list).toOption.map
        CheckedDocumentComputationStep.ofBooleanFirstFilled
    | .fragment => (checkDateFragmentFirstFilledComputation model ["Fj"] target list).toOption.map
        CheckedDocumentComputationStep.ofDateFragmentFirstFilled
    | .time => (checkTimeFirstFilledComputation model ["Fj"] target list).toOption.map
        CheckedDocumentComputationStep.ofTimeFirstFilled
    | .dateTime => (checkDateTimeFirstFilledComputation model ["Fj"] target list).toOption.map
        CheckedDocumentComputationStep.ofDateTimeFirstFilled
    | .date => (checkFullDateFirstFilledComputation model ["Fj"] target list).toOption.map
        CheckedDocumentComputationStep.ofFullDateFirstFilled
    | .dateRange => (checkDateRangeFirstFilledDirectComputation model ["Fj"] target
        (entities first second)).toOption.map CheckedDocumentComputationStep.ofDateRangeFirstFilledDirect
    | .enumeration => (elaborateEnumerationFirstFilledComputation model ["Fj"] target
        { first := .field (.direct (bare first)), rest := [.field (.direct (bare second))] }).toOption.map
        CheckedDocumentComputationStep.ofEnumerationFirstFilled).map CheckedScalarComputationStep.document

private def one : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 1, authoredScale := 0 }

private def guardStep? (target : FieldId) (guard : ComputationCondition) :
    Option (CheckedScalarComputationStep model) :=
  (elaborateNumericTargetComputationTable model ["Fj"] target [(some guard, one)]).toOption.map .number

/-- One kind's computations in the grid's authored order, every reader ahead of what it reads. -/
private def Kind.steps? (kind : Kind) : Option (List (CheckedScalarComputationStep model)) :=
  let x := kind.letter
  [guardStep? (kind.id 5) (.fieldFilled (kind.id 4)),
    guardStep? (kind.id 6) (.fieldNotFilled (kind.id 4)),
    kind.firstFilled? (kind.id 4) (x ++ "A") (x ++ "3"),
    kind.firstFilled? (kind.id 3) (x ++ "1") (x ++ "2")].mapM fun step => step

private def plan : CheckedScalarComputationPlan model :=
  (certifyScalarComputationPlan ((Kind.all.mapM Kind.steps?).get (by native_decide)).flatten).toOption.get
    (by native_decide)

/-- A `yyyy-MM` fragment cell: the month's first day at local midnight, or the format rejection. -/
private def fragmentRaw (declaration : FlatFieldDecl) (text : String) : RawCell :=
  match certifyOmittingDateInputField declaration, ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | .ok checked, some profile =>
      match checked.classifyStoredForModel model.baseYear text with
      | .admitted (.yearBearing (.omittedDay date)) =>
          match profile.resolveStoredDate? date.first.civil with
          | some value => .parsed (.temporal (.date value))
          | none => .rejected .dateFormat
      | .rejected cause => .rejected cause
      | _ => .rejected .dateFormat
  | _, _ => .rejected .dateFormat

private def classified (declaration : FlatFieldDecl) (text : String) : RawCell :=
  let fallback : RawCell := .rejected .dateFormat
  match declaration.policy.kind with
  | .boolean => classifyStoredBooleanText text
  | .temporal .date _ =>
      if declaration.toTemporalTargetPolicy?.map (·.partialMode) == some .yearOptional then
        fragmentRaw declaration text
      else match certifyFullDateInputField declaration with
        | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
        | .error _ => fallback
  | .enumeration => .parsed (.enum text)
  | .number _ => match text.toInt? with
      | some amount => .parsed (.num amount)
      | none => .rejected .malformed
  | .dateRange => (classifyStoredDateRangeForModel model.timeZoneId model.baseYear rangePolicy
      text).toOption.getD fallback
  | .temporal .time _ => match certifyTimeInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
      | .error _ => fallback
  | .temporal .dateTime _ => match certifyDateTimeInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
      | .error _ => fallback
  | _ => match certifyFullDateInputField declaration with
      | .ok checked => (checked.classifyStoredForModel model.timeZoneId text).toOption.getD fallback
      | .error _ => fallback

private def cell (name : String) (text : String) : Option ClassifiedCellInput := do
  let declaration ← model.fields.find? (·.name == name)
  pure { address := { field := declaration.id, path := [] }, stored := text
         raw := classified declaration text
         numericDecimal := (text.toInt?.filter fun _ => 5 ≤ declaration.id % 7).map
           ({ unscaled := ·, scale := 0 }) }

/-- One kind's three sources and the grid's seeds: `XA`, `XF` and both guards. -/
private def Kind.inputs (kind : Kind) (sources : List (Option String)) : List (String × String) :=
  let seeds : List (Option String) := match kind with
    | .boolean => [some "true", none]
    | .fragment => [some "2020-01", some "2021-01"]
    | .time => [some "01:02:03", some "02:03:04"]
    | .dateTime => [some "2020-01-01T01:02:03", some "2021-01-01T01:02:03"]
    | .date => [some "2020-01-01", some "2021-01-01"]
    | .dateRange => [some "2020-01-01/2020-01-02", some "2021-01-01/2021-01-02"]
    | .enumeration => [some "2", some "2"]
  (kind.names.zip (sources ++ seeds ++ [some "99", some "99"])).filterMap fun (name, text) =>
    text.map (name, ·)

private def valueOf? : ScalarComputationOutcome → Option (FieldId × String)
  | .number target (.accepted value) => some (target, toString value.unscaled)
  | .number target .noValue | .number target (.inheritedPoison _) => some (target, "-")
  | .document target (.boolean (.value value)) => some (target, toString value)
  | .document target (.dateFragment (.accepted stored)) => some (target, stored.text)
  | .document target (.time (.accepted stored)) => some (target, stored.text)
  | .document target (.dateTime (.accepted stored)) => some (target, stored.text)
  | .document target (.fullDate (.accepted stored)) => some (target, stored.text)
  | .document target (.dateRange (.accepted stored)) => some (target, stored.text)
  | .document target (.enumeration (.accepted stored)) => some (target, stored.text)
  | .document target (.boolean .noValue) | .document target (.boolean (.poison _))
  | .document target (.dateFragment .noValue) | .document target (.dateFragment (.poison _))
  | .document target (.time .noValue) | .document target (.time (.poison _))
  | .document target (.dateTime .noValue) | .document target (.dateTime (.poison _))
  | .document target (.fullDate .noValue) | .document target (.fullDate (.poison _))
  | .document target (.dateRange .noValue) | .document target (.dateRange (.poison _))
  | .document target (.enumeration .noValue) | .document target (.enumeration (.poison _)) =>
      some (target, "-")
  | .number _ (.rejected _ _) | .number _ (.invalidNoValue _) | .string _ _
  | .document _ (.dateTime (.errored _ _)) | .document _ (.fullDate (.errored _ _))
  | .document _ (.dateRange (.errored _ _)) | .document _ (.enumeration (.errored _ _))
  | .document _ (.dateFragment (.errored _ _)) => none

/-- Every kind's `XA`, `XF`, `KX` and `KNX`, over one document built from each kind's sources. -/
private def values? (sources : Kind → List (Option String)) : Option (List (List String)) := do
  let cells ← (Kind.all.flatMap fun kind => kind.inputs (sources kind)).mapM fun (name, text) =>
    cell name text
  let input ← (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  let found ← outcomes.mapM valueOf?
  Kind.all.mapM fun kind => [3, 4, 5, 6].mapM fun slot =>
    (found.find? (·.1 == kind.id slot)).map (·.2)

/-- Each kind's first, second and third source values in the grid's rows. -/
private def fresh : Kind → String
  | .boolean => "false" | .fragment => "2026-05" | .time => "08:30:00" | .dateTime => "2026-05-04T08:30:00"
  | .date => "2026-05-04" | .dateRange => "2026-05-04/2026-05-10" | .enumeration => "1"

private def third : Kind → String
  | .boolean => "true" | .fragment => "2026-07" | .time => "09:45:00" | .dateTime => "2026-07-08T09:45:00"
  | .date => "2026-07-08" | .dateRange => "2026-07-08/2026-07-10" | .enumeration => "3"

private def malformed : Kind → String
  | .boolean => "maybe" | .time => "99:99:99" | .enumeration => "9" | _ => "nonsense"

/- Rows `r1` and `r5`: `XF` reads the fresh `XA`, not its seed, and never reaches a malformed `X3`; the
filled guard fires. -/
example :
    values? (fun kind => [some (fresh kind), none, some (third kind)]) =
      some (Kind.all.map fun kind => [fresh kind, fresh kind, "1", "-"]) ∧
    values? (fun kind => [some (fresh kind), none, some (malformed kind)]) =
      some (Kind.all.map fun kind => [fresh kind, fresh kind, "1", "-"]) := by
  native_decide

/- Rows `r2` and `r3`: a cleared `XA` lets `XF` fall through to `X3`, while a poisoned one ends `XF`'s
scan with `X3` unread and reaches both guards as poison. -/
example :
    values? (fun kind => [none, none, some (third kind)]) =
      some (Kind.all.map fun kind => ["-", third kind, "1", "-"]) ∧
    values? (fun kind => [some (malformed kind), none, some (third kind)]) =
      some (Kind.all.map fun _ => ["-", "-", "-", "-"]) := by
  native_decide

/- Row `r4`: exhaustion clears both targets and only the unfilled guard fires. -/
example :
    values? (fun _ => [none, none, none]) = some (Kind.all.map fun _ => ["-", "-", "-", "1"]) := by
  native_decide

/-- An `MM` fragment target alone, in a model with or without a Base Year. -/
private def monthModel (baseYear : Option Int) : FlatModel :=
  { fields := [{
      id := 0
      groupPath := ["Fj"]
      name := "GM"
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "MM", partialMode := .yearOptional } }]
    timeZoneId := "Europe/Berlin"
    baseYear := baseYear }

/- A completed yearless fragment is read back as its month's first day in the Base Year, and with no
Base Year, which leaves the completion unmeasured, it fails closed as unreadable. -/
example :
    (match DocumentComputationReadBack.dateFragment (monthModel (some 2011)) 0
        (.accepted ⟨"03", by decide⟩) with
      | .ok cell => match cell.parsed with
          | some (.temporal (.date value)) => value.parts == { year := 2011, month := 3, day := 1 }
          | _ => false
      | .error _ => false) &&
    (match DocumentComputationReadBack.dateFragment (monthModel none) 0
        (.accepted ⟨"03", by decide⟩) with
      | .error .targetNotReadable => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.ScalarComputationPlanFirstFilled
