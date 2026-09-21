import A12Kernel.Elaboration.AddressedRepetitionComputation

namespace A12Kernel.Conformance.AddressedRepetitionComputation

private def outerPath : GroupPath := ["Root", "Rows"]
private def innerPath : GroupPath := outerPath ++ ["Items"]
private def fixedPath : GroupPath := innerPath ++ ["Fixed"]
private def asidePath : GroupPath := ["Root", "Aside"]
/-- `yyyy-MM-dd`: the date half only, so a time component is the temporal row's own separator. -/
private def dateComponents : TemporalComponents :=
  { year := true, month := true, day := true, hour := false, minute := false, second := false }
private def target : FlatFieldDecl :=
  { id := 1, groupPath := innerPath, name := "Target", repeatableScope := [10, 20]
    policy := { kind := .number { scale := 0, signed := true } }
    numericTargetConstraints := { maximum := some 22 } }
private def textDecl : FlatFieldDecl :=
  { target with id := 6, name := "Text", policy := { kind := .string }, numericTargetConstraints := {} }
private def whenDecl : FlatFieldDecl :=
  { target with id := 8, name := "When", policy := { kind := .temporal .date dateComponents }, numericTargetConstraints := {} }
private def stampDecl : FlatFieldDecl :=
  { target with id := 12, name := "Stamp", policy := { kind := .temporal .dateTime TemporalComponents.now }, numericTargetConstraints := {} }
private def spanDecl : FlatFieldDecl :=
  { target with id := 9, name := "Span", policy := { kind := .dateRange }, numericTargetConstraints := {}, dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }
private def model : FlatModel :=
  { fields := [target, { target with id := 2, name := "Base" },
      { target with id := 3, groupPath := fixedPath, name := "FixedField" },
      { target with id := 4, groupPath := ["Root"], name := "Scalar", repeatableScope := [] },
      { target with id := 5, groupPath := outerPath, name := "OuterTarget", repeatableScope := [10] },
      -- Non-Number sources for the widened operand set: one bound by the target's own scope and one
      -- bound by a disjoint repeatable level, which is the separator the scope rule must refuse.
      textDecl,
      { target with id := 7, groupPath := asidePath, name := "AsideText", repeatableScope := [30], policy := { kind := .string }, numericTargetConstraints := {} },
      -- A Date on that same disjoint level, so the difference endpoint's refusal is attributable to
      -- the scope rule rather than to the kind the String row already separates.
      { whenDecl with id := 10, groupPath := asidePath, name := "AsideWhen", repeatableScope := [30] },
      -- A second Date in the target's own row, so a two-endpoint difference addresses two distinct
      -- cells and each endpoint's read is separately observable.
      { whenDecl with id := 11, name := "Until" },
      -- A complete instant, which the day difference admits and the completed-period units refuse;
      -- the sub-day units need it, so one declaration separates all three families.
      stampDecl, { stampDecl with id := 13, name := "StampTwo" },
      -- A Number on the disjoint repeatable level. An aggregate list may name a nonrepeatable
      -- field outside the target's row, so this is what separates "outside the row" from "outside
      -- the target's scope" — only the second is refused.
      { target with id := 14, groupPath := asidePath, name := "AsideNum", repeatableScope := [30], numericTargetConstraints := {} },
      whenDecl, spanDecl]
    repeatableGroups := [
      { level := 10, path := outerPath, repeatability := some 3 },
      { level := 20, path := innerPath, repeatability := some 3 },
      { level := 30, path := asidePath, repeatability := some 3 }]
    baseYear := some 2020 }
private def repetition (path : GroupPath) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.currentRepetition { base := .absolute, groups := path })
private def field (name : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .relative 0, groups := [], field := name })
private def literal (value : Rat) : AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }
private def scalar : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .absolute, groups := ["Root"], field := "Scalar" })
private def mixed : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (.binary .multiply (repetition outerPath) (literal 10))
    (repetition innerPath)
private def operation (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
  checkAddressedRepetitionComputation model innerPath 1 expression
private def read (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  .ok (target.checkRaw (.parsed (.num (if address.path == [2, 3] then 7 else 9))))
private def evaluate? (expression : AuthoredNumericExpr SurfaceNumericAtom) (environment : Env) :
    Option (Sum EnvBindingError NumericComputationResult) := do
  let checked ← (operation expression).toOption
  match checked.evaluateAtEnvironmentWithRead read environment with
  | .ok value => some (.inr value)
  | .error (.environment error) => some (.inl error)
  | .error _ => none

example : evaluate? (repetition fixedPath) [(10, 2), (20, 3)] = some (.inr (.value 1)) ∧
    evaluate? (repetition ["Root"]) [(10, 2), (20, 3)] = some (.inr (.value 1)) ∧
    evaluate? mixed [(10, 2), (20, 3)] = some (.inr (.value 23)) ∧
    evaluate? (.binary .add (repetition innerPath) (field "Base")) [(10, 2), (20, 3)] =
      some (.inr (.value 10)) ∧
    evaluate? (.binary .add (repetition innerPath) scalar) [(10, 2), (20, 3)] =
      some (.inr (.value 12)) := by native_decide

example : evaluate? (repetition fixedPath) [(20, 3)] =
      some (.inl (.missingBinding 10)) ∧
    evaluate? (repetition innerPath) [(10, 0), (20, 3)] =
      some (.inl (.zeroBinding 10)) := by native_decide

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)
private def input : CheckedDocument model :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [2, 3] }, { group := 20, path := [2, 1] },
      { group := 20, path := [2, 2] }, { group := 20, path := [2, 4] }]
    cells := [] }).toOption.get (by native_decide)
private def outcomes? (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (List (List Nat × NumericTargetOutcome)) := do
  let checked ← (operation expression).toOption
  let outcomes ← (checked.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField.path, entry.outcome))

example : outcomes? mixed = some [
    ([2, 3], .rejected { unscaled := 23, scale := 0 } .aboveMaximum),
    ([2, 1], .accepted { unscaled := 21, scale := 0 }),
    ([2, 2], .accepted { unscaled := 22, scale := 0 }), ([2, 4], .noValue)] ∧
    outcomes? (repetition fixedPath) = some [
    ([2, 3], .accepted { unscaled := 1, scale := 0 }),
    ([2, 1], .accepted { unscaled := 1, scale := 0 }),
    ([2, 2], .accepted { unscaled := 1, scale := 0 }), ([2, 4], .noValue)] := by
  native_decide

example : ((operation mixed).toOption.map fun checked =>
    (checked.target.targetDeclaration.repeatableScope, checked.referencesField 1,
      checked.referencesField 2)) = some ([10, 20], false, false) ∧
    ((operation (.binary .add (repetition innerPath) (field "Base"))).toOption.map
      (·.referencesField 2)) = some true := by native_decide

example : (checkAddressedRepetitionComputation model ["Root"] 1 mixed).isOk = true ∧
    (match checkAddressedRepetitionComputation model ["Root"] 5 (repetition innerPath) with
      | .error error => some error
      | .ok _ => none) = some (.repetition (.repeatableGroupRequiresAddress innerPath)) ∧
    (operation (.binary .add (repetition innerPath) (field "Target"))).isOk = false ∧
    (operation (.binary .add (literal 1) (field "Base"))).isOk = false := by native_decide

example :
    let checked := (operation mixed).toOption.get (by native_decide)
    let source : BoundCurrentRepetitionSource := { path := innerPath, scope := [10, 20], level := some 20 }
    checked.target.admitsRepetitionOperand (.boundCurrentRepetition source) = true ∧
      checked.target.admitsRepetitionOperand (.boundCurrentRepetition { source with scope := [20] }) = false ∧
      checked.target.admitsRepetitionOperand (.boundCurrentRepetition { source with level := none }) = false ∧
      checked.target.admitsRepetitionOperand
        (.field { target with id := 2, name := "Base", repeatableScope := [] }) = false := by
  native_decide

/-- The widened source set: mixing with `CurrentRepetition` does not narrow which numeric source
kinds a repeatable Number target admits, measured against the Kernel on `BaseYear`, `Length`, and
`YearFromDate` beside a repetition operand and each alone
([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-numeric-source-kinds)).
The scope rule is the only gate, so `AsideText` — a String on a disjoint repeatable level — is
refused where the same atom on the target's own level is admitted. The temporal row carries a
component the declared format lacks as its own separator, so admission is not merely by kind. -/
example :
    let checked := (operation mixed).toOption.get (by native_decide)
    checked.target.admitsRepetitionOperand (.baseYear 2020) = true ∧
      checked.target.admitsRepetitionOperand (.stringLength { id := 6 }) = true ∧
      checked.target.admitsRepetitionOperand (.stringLength { id := 7 }) = false ∧
      checked.target.admitsRepetitionOperand
        (.temporalFieldPart { id := 8, kind := .date, components := dateComponents }
          (.date .year)) = true ∧
      checked.target.admitsRepetitionOperand
        (.temporalFieldPart { id := 8, kind := .date, components := dateComponents }
          (.time .hour)) = false := by
  native_decide

/-- The widened set is reachable from the authored surface, not only from the admission predicate.
Each row resolves a surface atom against the target's own declaring group, so a source in the
target's row elaborates where the nonrepeatable scalar resolver would have refused it. The
`AsideText` row is the separator: same atom shape, disjoint repeatable level, refused. -/
example :
    let len : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength { base := .relative 0, groups := [], field := "Text" })
    let asideLen : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength { base := .absolute, groups := asidePath, field := "AsideText" })
    let year : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.temporalFieldPart { base := .relative 0, groups := [], field := "When" } (.date .year))
    (operation (.binary .add (repetition innerPath) len)).isOk = true ∧
      (operation (.binary .add (repetition innerPath) (.atom .baseYear))).isOk = true ∧
      (operation (.binary .add (repetition innerPath) year)).isOk = true ∧
      (operation (.binary .add (repetition innerPath) asideLen)).isOk = false := by
  native_decide

/-- Each widened kind also **evaluates** in a row, so the arms added to the operand reader are
exercised rather than merely reachable. One read serves every source by field id: `Text` carries
four UTF-16 units, `When` carries 2021, and the repetition coordinate at `[(10, 2), (20, 3)]` is 3.
The Base Year row reads no cell at all, which is why it is the one kind with no scope to bind. -/
private def readTyped (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  .ok (if address.field == 6 then
      textDecl.checkRaw (.parsed (.str "abcd"))
    else if address.field == 8 then
      whenDecl.checkRaw (.parsed (.temporal (.date {
        instant := { epochMillis := 0 }
        parts := { year := 2021, month := 6, day := 1 }
        basis := .storedGregorian })))
    else target.checkRaw (.parsed (.num 9)))

example :
    let len : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength { base := .relative 0, groups := [], field := "Text" })
    let year : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.temporalFieldPart { base := .relative 0, groups := [], field := "When" } (.date .year))
    let run (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      ((operation expression).toOption.bind fun checked =>
        (checked.evaluateAtEnvironmentWithRead readTyped [(10, 2), (20, 3)]).toOption)
    run (.binary .add (repetition innerPath) len) = some (.value 7) ∧
      run (.binary .add (repetition innerPath) (.atom .baseYear)) = some (.value 2023) ∧
      run (.binary .add (repetition innerPath) year) = some (.value 2024) := by
  native_decide

/-- The three remaining single-source kinds, each authored through the surface and each carrying its
own refusal. `RangeAsNumber` answers the shared interval rule, so a reversed interval is refused on
a declaration the same expression otherwise admits; a DateRange endpoint component needs a DateRange
declaration, so the String field is refused in that position; and the Base-Year date component reads
no cell, matching the bare Base Year. -/
example :
    let span : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.dateRangeBoundPart { base := .relative 0, groups := [], field := "Span" }
        .start (.year))
    let badSpan : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.dateRangeBoundPart { base := .relative 0, groups := [], field := "Text" }
        .start (.year))
    let rng (start finish : Nat) : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringRange { base := .relative 0, groups := [], field := "Text" } start finish)
    (operation (.binary .add (repetition innerPath) (rng 1 2))).isOk = true ∧
      (operation (.binary .add (repetition innerPath) (rng 3 2))).isOk = false ∧
      (operation (.binary .add (repetition innerPath) span)).isOk = true ∧
      (operation (.binary .add (repetition innerPath) badSpan)).isOk = false ∧
      (operation (.binary .add (repetition innerPath)
        (.atom (.baseYearDatePart .direct .year)))).isOk = true := by
  native_decide

private def poisonBeforeMissingBinding (reverse : Bool) : Option (Sum EnvBindingError NumericComputationResult) := do
  let expression := if reverse then .binary .add (repetition innerPath) scalar
    else .binary .add scalar (repetition innerPath)
  let checked ← (operation expression).toOption
  match checked.evaluateAtEnvironmentWithRead
      (fun _ => .ok (target.checkRaw (.rejected .malformed))) [] with
  | .ok value => some (.inr value)
  | .error (.environment error) => some (.inl error)
  | .error _ => none

example : poisonBeforeMissingBinding false = some (.inr (.poison .malformed)) ∧
    poisonBeforeMissingBinding true = some (.inl (.missingBinding 10)) := by native_decide

example : evaluate? (.abs (repetition fixedPath)) [(10, 2), (20, 3)] =
    some (.inr (.value 1)) := by native_decide

example :
    let fractional := AuthoredNumericExpr.binary .multiply (repetition innerPath)
      (.literal { value := 3 / 2, authoredScale := 1 })
    (checkAddressedRepetitionComputation model innerPath 1 fractional).isOk = false ∧
      (checkAddressedRepetitionComputation model innerPath 1 fractional true).isOk = true := by
  native_decide

private def whenRef : SurfaceFieldPath := { base := .relative 0, groups := [], field := "When" }
private def textRef : SurfaceFieldPath := { base := .relative 0, groups := [], field := "Text" }
private def asideWhenRef : SurfaceFieldPath :=
  { base := .absolute, groups := asidePath, field := "AsideWhen" }
private def months (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (repetition innerPath) (.atom (.dateDifference .months left right))

/-- The completed-period difference is authorable beside the operand, and **each** of its two
endpoints answers the same scope rule a single-field source answers — which is the whole reason a
two-operand source needed its own admission arm rather than the single-field one. `AsideWhen` is the
separator: same Date declaration as `When`, disjoint repeatable level, refused in the endpoint
position that `When` occupies in the admitted row above it. `Now` is refused because this carrier's
row read carries no evaluation world. The Kernel admits the field pair beside the operand
([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-numeric-source-kinds)). -/
example :
    (operation (months (.field whenRef) (.field whenRef))).isOk = true ∧
      (operation (months (.field whenRef) (.baseYear .direct))).isOk = true ∧
      (operation (months (.field textRef) (.field whenRef))).isOk = false ∧
      (operation (months (.field whenRef) (.field asideWhenRef))).isOk = false ∧
      (operation (months (.field whenRef) .now)).isOk = false := by
  native_decide

private def untilRef : SurfaceFieldPath := { base := .relative 0, groups := [], field := "Until" }
/-- The exact instant is carried beside the decoded parts on purpose: the completed-period
    difference reads the parts and the day difference reads the instant, so a fixture that pinned
    both endpoints to one epoch would answer zero days while still answering the right months. -/
private def dateAt (epochDay : Nat) (year month day : Nat) : CheckedCell :=
  whenDecl.checkRaw (.parsed (.temporal (.date {
    instant := { epochMillis := Int.ofNat (epochDay * 86400000) }
    parts := { year := year, month := month, day := day }
    basis := .storedGregorian })))
/-- A complete instant on 1970-01-01 at the given hour, for the sub-day family. -/
private def instantAt (hour : Fin 24) : CheckedCell :=
  stampDecl.checkRaw (.parsed (.temporal (.dateTime
    { epochMillis := Int.ofNat (hour * 3600000) }
    { year := 1970, month := 1, day := 1 }
    { hour := hour, minute := 0, second := 0, valid := by omega }
    .storedGregorian)))

/-- `When` is 2021-06-01 and `Until` 2022-02-01, with `spoil` naming at most one of them as a
    rejected stored date so a single endpoint can be poisoned while the other stays clean. -/
private def readEndpoints (spoil : FieldId) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell :=
  .ok (if address.field == spoil then whenDecl.checkRaw (.rejected .dateFormat)
    else if address.field == 8 then dateAt 18779 2021 6 1
    else if address.field == 11 then dateAt 19024 2022 2 1
    else if address.field == 12 then instantAt 0
    else if address.field == 13 then instantAt 3
    else target.checkRaw (.parsed (.num 9)))

/-- Both endpoints are read, each at its own field, and either one's formal invalidity reaches the
result. The two poison rows are what separate that from a reader that resolves one cell and serves
it for every id: under such a reader the `Until`-only row would still answer 11. -/
example :
    let run (spoil : FieldId) (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      ((operation expression).toOption.bind fun checked =>
        (checked.evaluateAtEnvironmentWithRead (readEndpoints spoil) [(10, 2), (20, 3)]).toOption)
    run 0 (months (.field whenRef) (.field untilRef)) = some (.value 11) ∧
      run 0 (months (.field whenRef) (.baseYear .direct)) = some (.value (-14)) ∧
      run 8 (months (.field whenRef) (.field untilRef)) = some (.poison .dateFormat) ∧
      run 11 (months (.field whenRef) (.field untilRef)) = some (.poison .dateFormat) := by
  native_decide

/-- The dependency query reports a source that is not a plain field reference. Every row here
answered `false` while the query matched only the plain-field atom, which is the shape of an
under-report that fails nothing and reaches a consumer as a missing edge. -/
example :
    let refers (expression : AuthoredNumericExpr SurfaceNumericAtom) (field : FieldId) :=
      (operation expression).toOption.map (·.referencesField field)
    refers (.binary .add (repetition innerPath)
        (.atom (.stringLength { base := .relative 0, groups := [], field := "Text" }))) 6
        = some true ∧
      refers (.binary .add (repetition innerPath)
        (.atom (.temporalFieldPart { base := .relative 0, groups := [], field := "When" }
          (.date .year)))) 8 = some true ∧
      refers (months (.field whenRef) (.field untilRef)) 11 = some true ∧
      refers (months (.field whenRef) (.baseYear .direct)) 11 = some false ∧
      refers (.binary .add (repetition innerPath) (.atom .baseYear)) 8 = some false := by
  native_decide

private def stampRef : SurfaceFieldPath := { base := .relative 0, groups := [], field := "Stamp" }
private def stampTwoRef : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := "StampTwo" }
private def days (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (repetition innerPath) (.atom (.dayDifference left right))
private def hours (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (repetition innerPath) (.atom (.dateTimeDifference .hours left right))

/-- The day and sub-day families complete the three, and one declaration separates all of them: the
complete instant `Stamp` is admitted at the day and sub-day units and refused at the completed-period
one, while the date-only `When` is the mirror. Each endpoint still answers the scope rule, so the
disjoint-level Date is refused in either position. -/
example :
    (operation (days (.field whenRef) (.field untilRef))).isOk = true ∧
      (operation (days (.field stampRef) (.field stampRef))).isOk = true ∧
      (operation (days (.field whenRef) (.field asideWhenRef))).isOk = false ∧
      (operation (days (.field textRef) (.field untilRef))).isOk = false ∧
      (operation (hours (.field stampRef) (.field stampRef))).isOk = true ∧
      (operation (hours (.field whenRef) (.field untilRef))).isOk = false ∧
      (operation (hours (.field stampRef) (.field asideWhenRef))).isOk = false ∧
      (operation (months (.field stampRef) (.field stampRef))).isOk = false := by
  native_decide


/-- The day and sub-day families read their two endpoints the same way, and the fixture separates
which half each one consults: `When` and `Until` carry decoded parts eight months apart and exact
instants 245 days apart, so the completed-period answer above and this one cannot both come from the
same half. Each family poisons from either endpoint alone. -/
example :
    let run (spoil : FieldId) (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      ((operation expression).toOption.bind fun checked =>
        (checked.evaluateAtEnvironmentWithRead (readEndpoints spoil) [(10, 2), (20, 3)]).toOption)
    run 0 (days (.field whenRef) (.field untilRef)) = some (.value 248) ∧
      run 8 (days (.field whenRef) (.field untilRef)) = some (.poison .dateFormat) ∧
      run 11 (days (.field whenRef) (.field untilRef)) = some (.poison .dateFormat) ∧
      run 0 (hours (.field stampRef) (.field stampTwoRef)) = some (.value 6) ∧
      run 12 (hours (.field stampRef) (.field stampTwoRef)) = some (.poison .dateFormat) ∧
      run 13 (hours (.field stampRef) (.field stampTwoRef)) = some (.poison .dateFormat) := by
  native_decide

private def rowField (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }
private def asideNum : SurfaceFieldPath :=
  { base := .absolute, groups := asidePath, field := "AsideNum" }
private def scalarPath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Root"], field := "Scalar" }
private def aggregate (op : NumericAggregateOp) (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath) : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add (repetition innerPath) (.atom (.aggregate op { first, rest }))

/-- The direct field list answers the same scope rule one field answers, member by member, and the
nonrepeatable `Scalar` is what shows the rule is about *binding* rather than about the target's row:
it sits outside the row and is admitted, because an empty repeatable scope is bound by any scope,
while the Number on the disjoint repeatable level is refused. The Kernel agrees on both, refusing
the disjoint read as a missing wildcard, and its two list gates draw their own classes
([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-aggregate-operand-scope)). -/
example :
    (operation (aggregate .sum (rowField "Base") [scalarPath])).isOk = true ∧
      (operation (aggregate .minimum scalarPath [rowField "Base"])).isOk = true ∧
      (operation (aggregate .sum (rowField "Base") [asideNum])).isOk = false ∧
      (operation (aggregate .sum (rowField "Base") [rowField "Target"])).isOk = false ∧
      (operation (aggregate .sum (rowField "Base") [rowField "Base"])).isOk = false ∧
      (operation (aggregate .sum (rowField "Base") [])).isOk = false ∧
      (operation (aggregate .sum (rowField "Base") [rowField "Text"])).isOk = false := by
  native_decide

/-- Every member is read at its own declaration's scope in the same row, so the nonrepeatable member
answers from outside the row while the row-local one answers from inside it, and either one's formal
invalidity reaches the result. -/
example :
    let run (spoil : FieldId) (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      ((operation expression).toOption.bind fun checked =>
        (checked.evaluateAtEnvironmentWithRead (readEndpoints spoil) [(10, 2), (20, 3)]).toOption)
    run 0 (aggregate .sum (rowField "Base") [scalarPath]) = some (.value 21) ∧
      run 0 (aggregate .minimum (rowField "Base") [scalarPath]) = some (.value 12) ∧
      run 2 (aggregate .sum (rowField "Base") [scalarPath]) = some (.poison .dateFormat) ∧
      run 4 (aggregate .sum (rowField "Base") [scalarPath]) = some (.poison .dateFormat) := by
  native_decide

/-! ## The Kernel-calibrated one-level matrix

The examples above separate the carrier's mechanisms on a two-level fixture. This section replays the
retained one-level observation instead, so the numbers below are the real engine's and not this
account's: model `Src` with a nonrepeatable `Meta/Scalar` and a repeatable `Rows` declaring `Base`,
`Text`, `When`, `Until`, Base Year 2020, and five computations of the form
`CurrentRepetition(/Src/Rows) + <source>`
([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-source-kinds-runtime)).
-/

private def calibratedTarget : FlatFieldDecl :=
  { id := 100, groupPath := ["Src", "Rows"], name := "AltLen", repeatableScope := [50],
    policy := { kind := .number { scale := 0, signed := true } } }
private def calibratedText : FlatFieldDecl :=
  { calibratedTarget with id := 101, name := "Text", policy := { kind := .string } }
private def calibratedWhen : FlatFieldDecl :=
  { calibratedTarget with id := 102, name := "When", policy := { kind := .temporal .date dateComponents } }
private def calibratedModel : FlatModel :=
  { fields := [calibratedTarget, { calibratedTarget with id := 103, name := "Base" },
      { calibratedTarget with id := 104, groupPath := ["Src", "Meta"], name := "Scalar", repeatableScope := [] },
      calibratedText, calibratedWhen, { calibratedWhen with id := 105, name := "Until" }],
    repeatableGroups := [{ level := 50, path := ["Src", "Rows"], repeatability := some 20 }],
    baseYear := some 2020 }
private def calibratedOperation (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
  checkAddressedRepetitionComputation calibratedModel ["Src", "Rows"] 100 expression
private def rowsRepetition : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.currentRepetition { base := .absolute, groups := ["Src", "Rows"] })
private def rowPath (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }
private def metaScalar : SurfaceFieldPath :=
  { base := .absolute, groups := ["Src", "Meta"], field := "Scalar" }
private def calibratedDate (year month day : Nat) : CheckedCell :=
  calibratedWhen.checkRaw (.parsed (.temporal (.date {
    instant := { epochMillis := 0 }
    parts := { year := year, month := month, day := day }
    basis := .storedGregorian })))
private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }

/-- The three observed documents, as the reader each row's environment sees. -/
private inductive CalibratedDocument where
  | clean | degraded | noScalar
  deriving DecidableEq

private def calibratedRead (document : CalibratedDocument) (row : Nat) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell :=
  let scalar : CheckedCell :=
    match document with
    | .noScalar => emptyCell
    | _ => calibratedTarget.checkRaw (.parsed (.num 100))
  let text (value : String) : CheckedCell := calibratedText.checkRaw (.parsed (.str value))
  .ok <| match address.field, document, row with
    | 104, _, _ => scalar
    | _, .degraded, 1 => emptyCell
    | 102, .degraded, 2 => calibratedWhen.checkRaw (.rejected .dateFormat)
    | 101, _, 1 => text "abcd"
    | 101, _, 2 => text "xy"
    | 102, _, 1 => calibratedDate 2021 3 1
    | 102, _, 2 => calibratedDate 2020 1 1
    | 105, _, 1 => calibratedDate 2021 11 1
    | 105, _, 2 => calibratedDate 2022 7 1
    | 103, _, 1 => calibratedTarget.checkRaw (.parsed (.num 7))
    | 103, _, _ => calibratedTarget.checkRaw (.parsed (.num 11))
    | _, _, _ => emptyCell

/-- Each source answers at its own declaration's scope in the reading row, and the one nonrepeatable
member answers the same root cell from both rows — which is why the aggregate moves by the row's own
`Base` alone across rows, and by the shared `Scalar` alone across documents. Empty is zero in every
source that reads a cell; only formal invalidity poisons, and it poisons its own source in its own
row while the other four complete. -/
example :
    let run (document : CalibratedDocument) (row : Nat)
        (expression : AuthoredNumericExpr SurfaceNumericAtom) :=
      ((calibratedOperation expression).toOption.bind fun checked =>
        (checked.evaluateAtEnvironmentWithRead (calibratedRead document row) [(50, row)]).toOption)
    let len := AuthoredNumericExpr.binary .add rowsRepetition
      (.atom (.stringLength (rowPath "Text")))
    let year := AuthoredNumericExpr.binary .add rowsRepetition
      (.atom (.temporalFieldPart (rowPath "When") (.date .year)))
    let diff := AuthoredNumericExpr.binary .add rowsRepetition
      (.atom (.dateDifference .months (.field (rowPath "When")) (.field (rowPath "Until"))))
    let agg := AuthoredNumericExpr.binary .add rowsRepetition
      (.atom (.aggregate .sum { first := rowPath "Base", rest := [metaScalar] }))
    let baseYear := AuthoredNumericExpr.binary .add rowsRepetition (.atom .baseYear)
    -- clean
    (run .clean 1 len, run .clean 2 len) = (some (.value 5), some (.value 4)) ∧
      (run .clean 1 year, run .clean 2 year) = (some (.value 2022), some (.value 2022)) ∧
      (run .clean 1 diff, run .clean 2 diff) = (some (.value 9), some (.value 32)) ∧
      (run .clean 1 agg, run .clean 2 agg) = (some (.value 108), some (.value 113)) ∧
      (run .clean 1 baseYear, run .clean 2 baseYear) = (some (.value 2021), some (.value 2022)) ∧
      -- the nonrepeatable member alone moves, in both rows
      (run .noScalar 1 agg, run .noScalar 2 agg) = (some (.value 8), some (.value 13)) ∧
      -- every empty source answers zero rather than poisoning
      (run .degraded 1 len, run .degraded 1 year) = (some (.value 1), some (.value 1)) ∧
      (run .degraded 1 diff, run .degraded 1 agg) = (some (.value 1), some (.value 101)) ∧
      -- one malformed date poisons its own two sources and leaves the other three complete
      (run .degraded 2 year, run .degraded 2 diff) =
        (some (.poison .dateFormat), some (.poison .dateFormat)) ∧
      (run .degraded 2 len, run .degraded 2 agg) = (some (.value 4), some (.value 113)) ∧
      run .degraded 2 baseYear = some (.value 2022) := by
  native_decide

end A12Kernel.Conformance.AddressedRepetitionComputation
