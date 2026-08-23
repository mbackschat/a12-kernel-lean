import A12Kernel.Elaboration.AddressedDateRangeBoundPart

/-! # Addressed DateRange-endpoint component locks

One numeric Date component of a selected endpoint computed per instantiated row. The static cases
separate the three gates this placement adds to the component's own admission — a repeatable Number
target, the source at that same scope, and the measured scale-0 derived-scale gate — and the runtime
cases pin per-row values with exact addresses across both endpoint carriers.
-/

namespace A12Kernel.Conformance.AddressedDateRangeBoundPart

open A12Kernel

private def rangeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format separator : String) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def rowDates :=
  rangeField 1 "RowDates" ["Order", "Rows"] [10] "yyyy-MM-dd" "/"
private def rowMonths :=
  rangeField 2 "RowMonths" ["Order", "Rows"] [10] "MM" "/"
private def outerDates :=
  rangeField 3 "OuterDates" ["Order"] [] "yyyy-MM-dd" "/"

private def numberField (id : FieldId) (name : String)
    (scope : List RepeatableLevel) (scale : Nat) : FlatFieldDecl := {
  id, name, groupPath := (if scope.isEmpty then ["Order"] else ["Order", "Rows"])
  repeatableScope := scope
  policy := { kind := .number { scale, signed := false } }
}

private def target := numberField 4 "Component" [10] 0
private def scaledTarget := numberField 5 "ScaledComponent" [10] 2
private def rootTarget := numberField 6 "RootComponent" [] 0

private def model : FlatModel := {
  fields := [rowDates, rowMonths, outerDates, target, scaledTarget, rootTarget]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Rows"]
    repeatability := some 5
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def checked (targetField : FieldId) (source : SurfaceFieldPath)
    (bound : DateRangeBound) (part : DateNumericPart) :
    Except AddressedDateRangeBoundPartElabError
      (CheckedAddressedDateRangeBoundPart model) :=
  checkAddressedDateRangeBoundPart model ["Order", "Rows"] targetField source
    bound part

/- The exact profile admits all four components and the unconfigured yearless one admits month and
quarter, which is the component owner's rule reaching this placement unchanged. -/
example :
    (checked target.id (bare "RowDates") .start .month).isOk = true ∧
      (checked target.id (bare "RowDates") .finish .year).isOk = true ∧
      (checked target.id (bare "RowMonths") .start .quarter).isOk = true ∧
      (match checked target.id (bare "RowMonths") .start .year with
        | .error cause => cause.diagnostic? == some .wrongDateFormatForOp
        | .ok _ => false) = true := by
  native_decide

/- Every date component derives scale 0, so a fractional target is refused. The Kernel reports
`MVK_INVALID_COMPARE_DEC_PLACES` on this shape; the local class stays unmapped because it does not
distinguish that code's suppression branch. -/
example :
    (match checked scaledTarget.id (bare "RowDates") .start .month with
      | .error (.scaleMismatch 2 0) => true
      | _ => false) = true := by
  native_decide

/- Two placement gates remain the shared ones. A nonrepeatable target is not an addressed operation
at all, and this placement requires the source at the target's own scope — **a local narrowing**, not
a Kernel refusal: the Kernel admits a scalar endpoint computing a row Number, and SG5 owns that gap. -/
example :
    (match checkAddressedDateRangeBoundPart model ["Order"] rootTarget.id
        (bare "OuterDates") .start .month with
      | .error (.placement (.targetNotRepeatable path)) => path == rootTarget.path
      | _ => false) = true ∧
    (checked target.id (parent "OuterDates") .start .month).isOk = true := by
  native_decide

private def rows : List RowAddr :=
  (List.range 3).map fun offset => { group := 10, path := [offset + 1] }

private def storedCell (field : FieldId) (path : List Nat)
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
        | none => .empty
    | .error _ => .empty
}

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def outcomes? (source : SurfaceFieldPath) (bound : DateRangeBound)
    (part : DateNumericPart) (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← (checked target.id source bound part).toOption
  let input ← checkedDocument cells
  let executed ← (operation.execute input).toOption
  pure (executed.map fun entry => (entry.targetField, entry.outcome))

private def result? (source : SurfaceFieldPath) (bound : DateRangeBound)
    (part : DateNumericPart) (cells : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← (checked target.id source bound part).toOption
  let input ← checkedDocument cells
  (operation.executeResult input (fun _ => ()) []).toOption

private def addressAt (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) : StoredNumber := { unscaled, scale := 0 }

/- Per-row values over an exact carrier: each row reads its own range, the selected end decides, and
an unplaced row substitutes the same real zero every direct component read does. -/
example :
    outcomes? (bare "RowDates") .finish .month [
      storedCell rowDates.id [1] "2024-06-01/2024-07-31",
      storedCell rowDates.id [2] "2024-01-15/2024-03-15"
    ] = some [
      (addressAt target.id 1, .accepted (stored 7)),
      (addressAt target.id 2, .accepted (stored 3)),
      (addressAt target.id 3, .accepted (stored 0))
    ] := by
  native_decide

/- The same rows read at the start select the other end, so no row can silently take its peer's. -/
example :
    outcomes? (bare "RowDates") .start .month [
      storedCell rowDates.id [1] "2024-06-01/2024-07-31",
      storedCell rowDates.id [2] "2024-01-15/2024-03-15"
    ] = some [
      (addressAt target.id 1, .accepted (stored 6)),
      (addressAt target.id 2, .accepted (stored 1)),
      (addressAt target.id 3, .accepted (stored 0))
    ] := by
  native_decide

/- An unconfigured yearless carrier reaches its retained label per row rather than failing as a
non-exact profile, and the quarter follows the retained month. -/
example :
    outcomes? (bare "RowMonths") .finish .quarter [
      storedCell rowMonths.id [1] "03/07",
      storedCell rowMonths.id [2] "11/12"
    ] = some [
      (addressAt target.id 1, .accepted (stored 3)),
      (addressAt target.id 2, .accepted (stored 4)),
      (addressAt target.id 3, .accepted (stored 0))
    ] := by
  native_decide

/- A formally invalid range poisons its own row's target and leaves every other row alone, so one
bad cell never becomes a zero and never spreads. -/
example :
    outcomes? (bare "RowDates") .start .month [
      storedCell rowDates.id [1] "2024-07-31/2024-06-01",
      storedCell rowDates.id [2] "2024-01-15/2024-03-15"
    ] = some [
      (addressAt target.id 1, .inheritedPoison .dateRangeInvalid),
      (addressAt target.id 2, .accepted (stored 1)),
      (addressAt target.id 3, .accepted (stored 0))
    ] := by
  native_decide

/- The same yearless carrier over the probe's third measured pair, where start and finish share one
month, so the quarter follows that single label. -/
example :
    outcomes? (bare "RowMonths") .finish .quarter [
      storedCell rowMonths.id [1] "05/05"
    ] = some [
      (addressAt target.id 1, .accepted (stored 2)),
      (addressAt target.id 2, .accepted (stored 0)),
      (addressAt target.id 3, .accepted (stored 0))
    ] := by
  native_decide

/- The channel a poisoned operand reaches is `cleared`, not the error channel, and only a target
that was filled in the source is reported there. This is the exact channel shape the Kernel returns
for this row: cleared, not errored, and carrying no value. -/
example :
    (do
      let view ← result? (bare "RowDates") .start .month [
        storedCell rowDates.id [1] "2024-07-31/2024-06-01",
        { address := { field := target.id, path := [1] }, stored := "99"
          raw := .parsed (.num 99) },
        storedCell rowDates.id [2] "2024-06-01/2024-07-31"
      ]
      pure (view.cleared,
        view.withChanges.map fun entry => (entry.targetField, entry.value),
        view.withErrors)) =
      some (
        [addressAt target.id 1],
        [(addressAt target.id 2, stored 6), (addressAt target.id 3, stored 0)],
        []) := by
  native_decide

end A12Kernel.Conformance.AddressedDateRangeBoundPart
