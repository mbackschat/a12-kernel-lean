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
  fields := [indexDecl, rangeDecl, monthRangeDecl, headcountDecl, wantedDecl]
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

private def storedCell (field : FieldId) (row : Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path := [row] }
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
  storedCell indexDecl.id 1 "Sales",
  storedCell rangeDecl.id 1 "2024-06-01/2024-07-31",
  storedCell indexDecl.id 2 "Eng",
  storedCell rangeDecl.id 2 "2024-01-15/2024-03-15"
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
        storedCell indexDecl.id 1 "Eng",
        storedCell rangeDecl.id 1 "2024-06-01/2024-07-31",
        storedCell indexDecl.id 2 "Ops",
        storedCell rangeDecl.id 2 "2024-01-15/2024-03-15"
      ] = some (.value 0 .both) := by
  native_decide

/- A **duplicated key** and a **formally invalid matched cell** both reach UNKNOWN, and their causes
stay distinct: the duplicate is a column-level unavailability while the invalid range keeps its own
class. Collapsing either into the empty zero above would be the same wrong account. -/
example :
    operandFor (literalKeyed "RowRange") .start .month
        (baseline.map fun input =>
          if input.address == { field := indexDecl.id, path := [2] } then
            storedCell indexDecl.id 2 "Sales"
          else
            input) =
      some (.unknown .duplicateIndex) ∧
    operandFor (literalKeyed "RowRange") .start .month
        (baseline.map fun input =>
          if input.address == { field := rangeDecl.id, path := [1] } then
            storedCell rangeDecl.id 1 "2024-07-31/2024-06-01"
          else
            input) =
      some (.unknown .dateRangeInvalid) := by
  native_decide

/- An unconfigured yearless carrier reaches its retained label through the keyed read too, so the
projection is carrier-independent rather than exact-only. -/
example :
    operandFor (literalKeyed "RowMonths") .finish .quarter [
      storedCell indexDecl.id 1 "Sales",
      storedCell monthRangeDecl.id 1 "03/07"
    ] = some (.value 3 .fixed) := by
  native_decide

end A12Kernel.Conformance.SemanticIndexDateRange
