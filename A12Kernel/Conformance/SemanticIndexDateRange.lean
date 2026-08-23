import A12Kernel.Elaboration.SemanticIndexDateRange

/-! # Keyed DateRange endpoint-component locks

The static cases separate the three gates this operand adds to the shared semantic-index certificate
— a DateRange selected target, that declaration's own component exposure, and the index field's kind
staying free — and the runtime cases pin the measured four-state result domain, where a no-match row
and a matched-but-empty cell collapse to the same empty read while a duplicated key and a formally
invalid matched cell both reach UNKNOWN carrying distinct causes.
-/

namespace A12Kernel.Conformance.SemanticIndexDateRange

open A12Kernel

private def indexDecl : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Dept"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def rangeDecl : FlatFieldDecl := {
  id := 2
  groupPath := ["Order", "Rows"]
  name := "RowRange"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
  repeatableScope := [10]
}

private def monthRangeDecl : FlatFieldDecl := {
  id := 3
  groupPath := ["Order", "Rows"]
  name := "RowMonths"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "MM", separator := "/" }
  repeatableScope := [10]
}

private def headcountDecl : FlatFieldDecl := {
  id := 4
  groupPath := ["Order", "Rows"]
  name := "Headcount"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [10]
}

private def scalarRangeDecl : FlatFieldDecl := {
  id := 6
  groupPath := ["Order"]
  name := "ScalarRange"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def scalarMonthsDecl : FlatFieldDecl := {
  id := 7
  groupPath := ["Order"]
  name := "ScalarMonths"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "MM", separator := "/" }
}

private def wantedDecl : FlatFieldDecl := {
  id := 5
  groupPath := ["Order"]
  name := "WantedDept"
  policy := { kind := .string }
}

private def rows : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Rows"]
  repeatability := some 3
  indexField := some 1
}

private def model : FlatModel := {
  fields := [
    indexDecl, rangeDecl, monthRangeDecl, headcountDecl, wantedDecl,
    scalarRangeDecl, scalarMonthsDecl
  ]
  repeatableGroups := [rows]
}

private def inRows (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order", "Rows"], field }

private def literalKeyed (field : String) : SurfaceSemanticIndex :=
  { target := inRows field, key := .literal (.text "Sales") }

private def fieldKeyed (field : String) : SurfaceSemanticIndex := {
  target := inRows field
  key := .field { base := .absolute, groups := ["Order"], field := "WantedDept" }
}

private def checked (authored : SurfaceSemanticIndex) (bound : DateRangeBound)
    (part : DateNumericPart) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeBoundPart model) :=
  checkSemanticIndexDateRangeBoundPart model ["Order"] authored bound part

/- The index field is a String and the selected target a DateRange, which is the measured
independence: both key forms are admitted at a nonrepeatable locus. -/
example :
    (checked (literalKeyed "RowRange") .start .month).isOk = true ∧
      (checked (fieldKeyed "RowRange") .finish .year).isOk = true := by
  native_decide

/- The exposure gate is the selected declaration's own component set, so an unconfigured yearless
target admits month and quarter while refusing day and year. That is the direct component owner's
rule reaching this source rather than a second gate. -/
example :
    (checked (literalKeyed "RowMonths") .start .quarter).isOk = true ∧
      (checked (literalKeyed "RowMonths") .finish .month).isOk = true ∧
      (match checked (literalKeyed "RowMonths") .start .year with
        | .error (.boundPartNotExposed path part) =>
            path == monthRangeDecl.path && part == .year
        | _ => false) = true ∧
      (match checked (literalKeyed "RowMonths") .start .day with
        | .error (.boundPartNotExposed _ _) => true
        | _ => false) = true := by
  native_decide

/- A selected target of another kind fails closed before any exposure question, and this project maps
neither local class to a Kernel code: the admission measurement established that the operand shape is
accepted, not which code its rejections carry. -/
example :
    (match checked (literalKeyed "Headcount") .start .month with
      | .error error =>
          error == .selectedTargetNotDateRange headcountDecl.path &&
            error.diagnostic? == none
      | .ok _ => false) = true := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def storedAt (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw :=
    match model.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
              policy stored).toOption.getD .empty
        | none => .parsed (.str stored)
    | .error _ => .parsed (.str stored)
}

/-- Two departments, each carrying one exact range. Every case below perturbs exactly one cell of
this baseline, so a difference in outcome is attributable to that perturbation. -/
private def baseline : List ClassifiedCellInput := [
  storedAt indexDecl.id [1] "Sales",
  storedAt rangeDecl.id [1] "2024-06-01/2024-07-31",
  storedAt indexDecl.id [2] "Eng",
  storedAt rangeDecl.id [2] "2024-01-15/2024-03-15"
]

private def operandFor (authored : SurfaceSemanticIndex)
    (bound : DateRangeBound) (part : DateNumericPart)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let operation ← (checked authored bound part).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] }
    ]
    cells }).toOption
  let preliminary ← document.applyFullIndexPreliminary.toOption
  (operation.resolvePreliminaryNumericOperand preliminary
    { read := fun _ => .empty }).toOption

/- The keyed row decides the component: the literal selects the Sales row and reads its own endpoint,
not the physically first one, and the two ends stay distinct. -/
example :
    operandFor (literalKeyed "RowRange") .start .month baseline =
        some (.value 6 .fixed) ∧
      operandFor (literalKeyed "RowRange") .finish .month baseline =
        some (.value 7 .fixed) := by
  native_decide

/- A **matched-but-empty cell** (first) and **no matching row at all** (second) collapse to the same
empty read, which the component's own symmetric rule turns into a fillable zero. This is the measured
collapse, and it is the pair a wrong account would separate. -/
example :
    operandFor (literalKeyed "RowRange") .start .month
        (baseline.filter fun input => input.address.field != rangeDecl.id) =
      some (.value 0 .both) ∧
    operandFor (literalKeyed "RowRange") .start .month [
        storedAt indexDecl.id [1] "Eng",
        storedAt rangeDecl.id [1] "2024-06-01/2024-07-31",
        storedAt indexDecl.id [2] "Ops",
        storedAt rangeDecl.id [2] "2024-01-15/2024-03-15"
      ] = some (.value 0 .both) := by
  native_decide

/- A **duplicated key** and a **formally invalid matched cell** both reach UNKNOWN, and their causes
stay distinct: the duplicate is a column-level unavailability while the invalid range keeps its own
class. Collapsing either into the empty zero above would be the same wrong account. -/
example :
    operandFor (literalKeyed "RowRange") .start .month
        (baseline.map fun input =>
          if input.address == { field := indexDecl.id, path := [2] } then
            storedAt indexDecl.id [2] "Sales"
          else
            input) =
      some (.unknown .duplicateIndex) ∧
    operandFor (literalKeyed "RowRange") .start .month
        (baseline.map fun input =>
          if input.address == { field := rangeDecl.id, path := [1] } then
            storedAt rangeDecl.id [1] "2024-07-31/2024-06-01"
          else
            input) =
      some (.unknown .dateRangeInvalid) := by
  native_decide

/- An unconfigured yearless carrier reaches its retained label through the keyed read too, so the
projection is carrier-independent rather than exact-only. -/
example :
    operandFor (literalKeyed "RowMonths") .finish .quarter [
      storedAt indexDecl.id [1] "Sales",
      storedAt monthRangeDecl.id [1] "03/07"
    ] = some (.value 3 .fixed) := by
  native_decide

private def equality (keyedField : String) (directSource : FieldId)
    (keyedFirst : Bool) (comparison : EqualityOp) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeEquality model) :=
  elaborateSemanticIndexDateRangeEquality model ["Order"]
    (literalKeyed keyedField) [] directSource keyedFirst comparison

/- The component gate is the direct carrier's own declaration-level rule and is symmetric in the
authored order, so an equal-component pair crosses on either side and a mismatched one is refused
identically. The mismatch class stays unmapped for the same reason the other two do. -/
example :
    (equality "RowRange" scalarRangeDecl.id true .equal).isOk = true ∧
      (equality "RowRange" scalarRangeDecl.id false .notEqual).isOk = true ∧
      (match equality "RowRange" scalarMonthsDecl.id true .equal with
        | .error error =>
            (match error with
              | .componentMismatch _ _ => true
              | _ => false) && error.diagnostic? == none
        | .ok _ => false) = true ∧
      (equality "RowMonths" scalarMonthsDecl.id true .equal).isOk = true := by
  native_decide

/- A repeatable direct operand beside the keyed one keeps its **own** resolution class at a
nonrepeatable locus rather than becoming a comparability failure, which is what lets a consumer tell
an unbound level from an incomparable profile. -/
example :
    (match equality "RowRange" rangeDecl.id true .equal with
      | .error (.directSource (.source _)) => true
      | _ => false) = true := by
  native_decide

private def equalityResult? (directSource : FieldId) (keyedFirst : Bool)
    (comparison : EqualityOp) (cells : List ClassifiedCellInput) :
    Option DirectDateRangeComparisonResult := do
  let operation ← (equality "RowRange" directSource keyedFirst
    comparison).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] }
    ]
    cells }).toOption
  let preliminary ← document.applyFullIndexPreliminary.toOption
  (operation.evaluate preliminary { read := fun _ => .empty }).toOption

/- The keyed row is compared against the scalar operand by retained identity: the Sales row's own
range decides, and the Eng row's differing range never reaches the verdict. -/
example :
    (equalityResult? scalarRangeDecl.id true .equal
        (storedAt scalarRangeDecl.id [] "2024-06-01/2024-07-31" :: baseline)).map
      (·.verdict) = some (.fired .value) ∧
    (equalityResult? scalarRangeDecl.id true .equal
        (storedAt scalarRangeDecl.id [] "2024-01-15/2024-03-15" :: baseline)).map
      (·.verdict) = some .notFired := by
  native_decide

/- The authored order is retained in the result rather than normalized, so an Explain consumer
recovers which side was keyed even where the verdict is symmetric. -/
example :
    (equalityResult? scalarRangeDecl.id false .equal
        (storedAt scalarRangeDecl.id [] "2024-01-15/2024-03-15" :: baseline)).map
      (fun result => (result.left, result.right)) =
    (equalityResult? scalarRangeDecl.id true .equal
        (storedAt scalarRangeDecl.id [] "2024-01-15/2024-03-15" :: baseline)).map
      (fun result => (result.right, result.left)) := by
  native_decide

/- Emptiness on either side leaves both directions unfired, and a formally invalid keyed row reaches
UNKNOWN rather than an error, so the keyed operand is read through the same rules a direct one is. -/
example :
    (equalityResult? scalarRangeDecl.id true .equal baseline).map (·.verdict) =
        some .notFired ∧
      (equalityResult? scalarRangeDecl.id true .notEqual baseline).map
        (·.verdict) = some .notFired ∧
      (equalityResult? scalarRangeDecl.id true .equal
          (storedAt scalarRangeDecl.id [] "2024-06-01/2024-07-31" ::
            baseline.map fun input =>
              if input.address == { field := rangeDecl.id, path := [1] } then
                storedAt rangeDecl.id [1] "2024-07-31/2024-06-01"
              else
                input)).map (·.verdict) = some .unknown := by
  native_decide

private def boundComparison (keyedField : String) (keyedBound : DateRangeBound)
    (directSource : FieldId) (directBound : DateRangeBound) (keyedFirst : Bool)
    (comparison : TemporalComparisonOp) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeBoundComparison model) :=
  elaborateSemanticIndexDateRangeBoundComparison model ["Order"]
    (literalKeyed keyedField) keyedBound directSource directBound keyedFirst
    comparison

/- The gate is the ordinary direct temporal admission rule, so this unconfigured model admits an
exact pair and a yearless pair but refuses the mixed-year one on either side. The refusal class stays
unmapped for the same reason the family's other local classes do. -/
example :
    (boundComparison "RowRange" .start scalarRangeDecl.id .start true
        .before).isOk = true ∧
      (boundComparison "RowMonths" .finish scalarMonthsDecl.id .start false
        .after).isOk = true ∧
      (match boundComparison "RowRange" .start scalarMonthsDecl.id .start true
          .before with
        | .error error =>
            (match error with
              | .boundsNotComparable _ _ => true
              | _ => false) && error.diagnostic? == none
        | .ok _ => false) = true ∧
      (match boundComparison "RowMonths" .start scalarRangeDecl.id .start true
          .before with
        | .error (.boundsNotComparable _ _) => true
        | _ => false) = true := by
  native_decide

private def comparisonResult? (keyedField : String)
    (keyedBound : DateRangeBound) (directSource : FieldId)
    (directBound : DateRangeBound) (keyedFirst : Bool)
    (comparison : TemporalComparisonOp) (cells : List ClassifiedCellInput) :
    Option DateRangeBoundPairResult := do
  let operation ← (boundComparison keyedField keyedBound directSource
    directBound keyedFirst comparison).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] }
    ]
    cells }).toOption
  let preliminary ← document.applyFullIndexPreliminary.toOption
  (operation.evaluate preliminary { read := fun _ => .empty }).toOption

/-- The scalar range straddles the keyed Sales row, so the *selected* scalar end changes the answer
while everything else stays fixed. -/
private def scalarExact : List ClassifiedCellInput :=
  storedAt scalarRangeDecl.id [] "2024-05-01/2024-12-31" :: baseline

/- The keyed row's own endpoint decides, and which end of the direct operand is selected decides
too: the Sales row starts after the scalar's start but not after its finish. -/
example :
    (comparisonResult? "RowRange" .start scalarRangeDecl.id .start true
        .after scalarExact).map (fun result =>
          match result with
          | .exact _ _ verdict => verdict
          | .yearless _ _ _ => .unknown) = some (.fired .value) ∧
      (comparisonResult? "RowRange" .start scalarRangeDecl.id .finish true
          .after scalarExact).map (fun result =>
            match result with
            | .exact _ _ verdict => verdict
            | .yearless _ _ _ => .unknown) = some .notFired := by
  native_decide

/- The authored order is retained rather than normalized, so the two observations arrive in the
authored slots and a directional operator is not silently mirrored. -/
example :
    (comparisonResult? "RowRange" .start scalarRangeDecl.id .start false
        .after scalarExact).map (fun result =>
          match result with
          | .exact left right verdict => (left, right, verdict)
          | .yearless _ _ _ => (.empty, .empty, .unknown)) =
      (comparisonResult? "RowRange" .start scalarRangeDecl.id .start true
          .before scalarExact).map (fun result =>
            match result with
            | .exact left right verdict => (right, left, verdict)
            | .yearless _ _ _ => (.empty, .empty, .unknown)) := by
  native_decide

/- The yearless domain compares retained labels completed by their authored position, so a month-only
finish reaches the greatest day that month can ever have and no year is manufactured. -/
example :
    (comparisonResult? "RowMonths" .finish scalarMonthsDecl.id .start true
        .after [
          storedAt indexDecl.id [1] "Sales",
          storedAt monthRangeDecl.id [1] "03/07",
          storedAt scalarMonthsDecl.id [] "05/09"
        ]).map (fun result =>
          match result with
          | .yearless left right verdict => (left, right, verdict)
          | .exact _ _ _ => (.empty, .empty, .unknown)) =
      some (.value { month := 7, day := 31 }, .value { month := 5, day := 1 },
        .fired .value) := by
  native_decide

/- A formally invalid keyed row reaches UNKNOWN through the comparison too, and an absent scalar
leaves the comparison unfired, so neither operand shape gets its own emptiness rule. -/
example :
    (comparisonResult? "RowRange" .start scalarRangeDecl.id .start true .after
        (storedAt scalarRangeDecl.id [] "2024-05-01/2024-12-31" ::
          baseline.map fun input =>
            if input.address == { field := rangeDecl.id, path := [1] } then
              storedAt rangeDecl.id [1] "2024-07-31/2024-06-01"
            else
              input)).map (fun result =>
                match result with
                | .exact _ _ verdict => verdict
                | .yearless _ _ _ => .notFired) = some .unknown ∧
      (comparisonResult? "RowRange" .start scalarRangeDecl.id .start true .after
        baseline).map (fun result =>
          match result with
          | .exact _ _ verdict => verdict
          | .yearless _ _ _ => .unknown) = some .notFired := by
  native_decide

end A12Kernel.Conformance.SemanticIndexDateRange
