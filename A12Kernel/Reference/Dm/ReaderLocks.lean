import A12Kernel.Reference.Dm.Document

/-! # Locks for the DM-JSON document reader

The reader stands where the Kernel's document conversion stands, so it owns the conversion's choices:
a Number text the conversion parses becomes decimal-valued and is read through the runtime rendering
(spec §4, storage regimes), a leading-zero value on a field allowing leading zeros stays text, a
Boolean token is read regardless of case, and a JSON `null` is a field present without a value. Each
case pins one choice against the reading that treats the document's text as user input.
-/

namespace A12Kernel.Dm.ReaderLocks

open Lean A12Kernel A12Kernel.Dm

/- The conversion grammar is Java `BigDecimal`'s: a sign, an exponent and a bare point are accepted,
and the scale is the written fraction less the exponent. -/
example :
    [convertedDecimal? "30" == some { unscaled := 30, scale := 0 },
     convertedDecimal? "+5" == some { unscaled := 5, scale := 0 },
     convertedDecimal? "-2.50" == some { unscaled := -250, scale := 2 },
     convertedDecimal? "1e5" == some { unscaled := 1, scale := -5 },
     convertedDecimal? ".5" == some { unscaled := 5, scale := 1 },
     convertedDecimal? "12a" == none,
     convertedDecimal? "" == none].all id := by
  native_decide

private def amount (constraints : NumericTargetConstraints) : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Amount", numericTargetConstraints := constraints
    policy := { kind := .number { scale := 2, signed := true } } }

private def model (declaration : FlatFieldDecl) : FlatModel := { fields := [declaration] }

private def classified (declaration : FlatFieldDecl) (stored : String) : Option ClassifiedCellInput :=
  (classifyStored (model declaration) declaration { field := 0, path := [] } stored).toOption

/- `30` on a field declaring two minimum fraction digits is read as `30.00` and is clean, where the
same text taken as user input lacks its separator; a leading-zero value on a field allowing leading
zeros keeps the text regime. -/
example :
    [(classified (amount { minFractionalDigits := 2 }) "30").map (·.raw) ==
       some (.parsed (.num 30)),
     (classified (amount { minFractionalDigits := 2 }) "30").bind (·.numericDecimal) ==
       some { unscaled := 30, scale := 0 },
     (classified (amount { leadingZerosAllowed := true }) "007").bind (·.numericDecimal) == none].all id := by
  native_decide

private def flag : FlatFieldDecl := { id := 0, groupPath := ["Order"], name := "Flag", policy := { kind := .boolean } }

/- A Boolean token is read regardless of case. -/
example :
    (classified flag "TRUE").map (·.stored) = some "true" := by
  native_decide

/- A JSON `null` places the field present and empty; a missing key places nothing. -/
example :
    let dm : DmModel := { flat := model flag, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    [((readDocument dm (Json.mkObj [("Order", Json.mkObj [("Flag", Json.null)])])).toOption.map
        (·.data.cells.map (·.raw))) == some [.presentEmpty],
     ((readDocument dm (Json.mkObj [("Order", Json.mkObj [])])).toOption.map
        (·.data.cells.length)) == some 0].all id := by
  native_decide

/- An object member the model declares no field below is refused, not read as an empty group. -/
example :
    let dm : DmModel := { flat := model flag, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    [((readDocument dm (Json.mkObj [("Order", Json.mkObj [("Typo", Json.mkObj [])])])).toOption.map
        (·.refusals.length)) == some 1,
     ((readDocument dm (Json.mkObj [("Nope", Json.mkObj [])])).toOption.map (·.refusals.length)) == some 1,
     ((readDocument dm (Json.mkObj [("Order", Json.mkObj [])])).toOption.map (·.refusals.length)) ==
        some 0].all id := by
  native_decide

/- The model file writes its Base Year as a string; an integer-only read silently dropped it, and a
yearless list beside a dated one then failed the component-set gate the Base Year supplements. -/
example :
    let read (info : Json) := (readModel (Json.mkObj [("content", Json.mkObj [("modelInfo", info),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[])])])])).toOption.map (·.flat.baseYear)
    [read (Json.mkObj [("baseYear", "2024")]) == some (some 2024),
     read (Json.mkObj []) == some none,
     read (Json.mkObj [("baseYear", Json.null)]) == some none,
     read (Json.mkObj [("baseYear", "next")]) == none].all id := by
  native_decide

private def clockField (kind : TemporalKind) : FlatFieldDecl := {
  id := 0, groupPath := ["Order"], name := "Clock"
  policy := { kind := .temporal kind TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" } }

private def clockRead (kind : TemporalKind) (zone text : String) :
    Option (Int × Nat × Nat × Nat) := do
  let field := clockField kind
  let cell ← (classifyStored { fields := [field], timeZoneId := zone } field
    { field := 0, path := [] } text).toOption
  match cell.raw with
  | .parsed (.temporal (.time instant clock)) =>
      pure (instant.epochMillis, clock.hour, clock.minute, clock.second)
  | _ => none

/- The format owns the parser on all three declared kinds (cross-kind runtime checkpoint).
The Berlin anchor is an internal model-zone check, not a new external observation. -/
example : [.date, .time, .dateTime].all (fun kind =>
    clockRead kind "UTC" "12:30:00" == some (45000000, 12, 30, 0) &&
    clockRead kind "Europe/Berlin" "12:30:00" == some (41400000, 12, 30, 0) &&
    (classified (clockField kind) "2024-03-05").map (·.raw) == some (.rejected .dateFormat) &&
    (classified (clockField kind) "24:00:00").map (·.raw) == some (.rejected .dateFormat) &&
    (classified (clockField kind) "").map (·.raw) == some .presentEmpty) := by
  native_decide

example : clockRead .date "unsupported-zone" "12:30:00" = none := by native_decide

private def repeatedClocks : Option (List (CellAddr × RawCell)) := do
  let field := { (clockField .dateTime) with
    groupPath := ["Order", "Rows"], repeatableScope := [10] }
  let dm : DmModel := {
    flat := {
      fields := [field], timeZoneId := "UTC"
      repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 2 }] }
    rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Order", Json.mkObj [
    ("Rows", Json.arr #[Json.mkObj [("Clock", "12:30:00")],
      Json.mkObj [("Clock", "2024-03-05")]])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  if !checked.temporallyCoherent then none
  pure (input.data.cells.map fun cell => (cell.address, cell.raw))

example : (repeatedClocks.map fun (cells : List (CellAddr × RawCell)) =>
    cells.map (·.1) == [{ field := 0, path := [1] }, { field := 0, path := [2] }] &&
    match (cells.map fun cell => cell.2 : List RawCell) with
    | [.parsed (.temporal (.time _ clock)), .rejected .dateFormat] => clock.hour == 12
    | _ => false) = some true := by native_decide

private def rowModel : DmModel := {
  flat := {
    fields := [{ id := 0, name := "Value", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }],
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
  rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rowInput (rows : Array Json) : Option DmDocument :=
  (readDocument rowModel (Json.mkObj [("Form", Json.mkObj [("Rows", Json.arr rows)])])).toOption

example : (rowInput #[.null, Json.mkObj [("Value", .str "kept")], .null]).map
    (fun input => (input.data.instantiatedRows, input.data.cells.map (·.address), input.refusals.length)) =
    some ([{ group := 10, path := [1] }], [{ field := 0, path := [1] }], 0) := by
  native_decide

private def rowShape (rows : Array Json) : Option (List RowAddr × List CellAddr × Nat) :=
  (rowInput rows).map fun input =>
    (input.data.instantiatedRows, input.data.cells.map (·.address), input.refusals.length)

example : rowShape #[] = some ([], [], 0) ∧
    rowShape #[.null, .bool false, toJson (7 : Nat), .str "x", .arr #[]] = some ([], [], 0) ∧
    rowShape #[.null, .bool true, Json.mkObj [("Value", .str "a")], .arr #[],
      Json.mkObj [("Value", .str "b")], .null] =
      some ([{ group := 10, path := [1] }, { group := 10, path := [2] }],
        [{ field := 0, path := [1] }, { field := 0, path := [2] }], 0) := by native_decide

example : rowShape #[Json.mkObj [], .null, Json.mkObj [("Value", .null)]] =
      some ([{ group := 10, path := [1] }, { group := 10, path := [2] }],
        [{ field := 0, path := [2] }], 0) ∧
    (rowInput #[Json.mkObj [("Value", .null)]]).map (·.data.cells.map (·.raw)) =
      some [.presentEmpty] ∧
    (rowInput #[Json.mkObj [("Unknown", .str "x")]]).map (·.refusals.length) = some 1 := by
  native_decide

private def nestedRowModel : DmModel := { rowModel with flat := {
  fields := [{ id := 0, name := "Value", groupPath := ["Form", "Rows", "Children"], repeatableScope := [10, 20], policy := { kind := .string } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3 },
    { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 3 }] } }

private def nestedRows : Option DmDocument :=
  let child := Json.mkObj [("Value", .str "kept")]
  (readDocument nestedRowModel (Json.mkObj [("Form", Json.mkObj [("Rows", Json.arr #[
    .null, Json.mkObj [], Json.mkObj [("Children", .arr #[.null, child])],
    .null, Json.mkObj [("Children", .arr #[child, .null, child, .null])]])])])).toOption

example : nestedRows.map (fun input =>
    (input.data.instantiatedRows, input.data.cells.map (·.address), input.refusals.length)) =
    some ([{ group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [2, 1] }, { group := 10, path := [3] },
      { group := 20, path := [3, 1] }, { group := 20, path := [3, 2] }],
      [{ field := 0, path := [2, 1] }, { field := 0, path := [3, 1] },
        { field := 0, path := [3, 2] }], 0) := by native_decide

private def readEnumDefault (value : Option Json) : Except String (Option String) := do
  let body := Json.mkObj ([("values", .arr #[Json.mkObj [("value", "a")],
    Json.mkObj [("value", "b")]])] ++ value.toList.map ("sValue", ·))
  let field ← readFieldType 0 ["Form"] "Key" [] (Json.mkObj [("fieldType",
    Json.mkObj [("type", "EnumerationType"), ("EnumerationType", body)])])
  pure (field.enumeration.bind (·.defaultStoredToken))

example : (readEnumDefault (some "a")).toOption = some (some "a") ∧
    (readEnumDefault (some "b")).toOption = some (some "b") ∧
    (readEnumDefault none).toOption = some none ∧
    (readEnumDefault (some .null)).toOption = some none ∧
    (readEnumDefault (some "")).toOption = some none := by native_decide

example : [Json.str "outside", toJson (1 : Nat), Json.bool true,
    Json.arr #[], Json.mkObj []].all (fun value => !(readEnumDefault (some value)).isOk) := by
  native_decide

end A12Kernel.Dm.ReaderLocks
