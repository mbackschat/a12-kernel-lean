import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Model

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
the scale is the written fraction less the exponent, and the digits are Java's BMP decimal digits. A
scale beyond the measured profile is refused rather than read, while a scale outside `int`, here
reached once through the fraction alone, keeps the text (K16 rows `d01`, `e01`, `e07`, `e11`, `e12`). -/
example :
    [convertDocumentNumber "30" == .decimal { unscaled := 30, scale := 0 },
     convertDocumentNumber "+5" == .decimal { unscaled := 5, scale := 0 },
     convertDocumentNumber "-2.50" == .decimal { unscaled := -250, scale := 2 },
     convertDocumentNumber "1e5" == .decimal { unscaled := 1, scale := -5 },
     convertDocumentNumber ".5" == .decimal { unscaled := 5, scale := 1 },
     convertDocumentNumber "\u0663.\u0665" == .decimal { unscaled := 35, scale := 1 },
     convertDocumentNumber "1e1001" == .decimal { unscaled := 1, scale := -1001 },
     convertDocumentNumber "1e-100000" == .decimal { unscaled := 1, scale := 100000 },
     convertDocumentNumber "1e100001" == .beyondProfile,
     convertDocumentNumber "1e2147483648" == .beyondProfile,
     convertDocumentNumber "1e-2147483647" == .beyondProfile,
     convertDocumentNumber "1e2147483649" == .text,
     convertDocumentNumber "1e-2147483648" == .text,
     convertDocumentNumber "0.5e-2147483647" == .text,
     convertDocumentNumber "12a" == .text,
     convertDocumentNumber "1e" == .text,
     convertDocumentNumber "1.2.3" == .text,
     convertDocumentNumber "" == .text].all id := by
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

/- An object member the model declares no field below is dropped, as the Kernel's conversion drops
it ([checkpoint](../../../docs/sources/domain-ingestion-probes.md#src-undeclared-document-members));
an undeclared array stays refused. -/
example :
    let dm : DmModel := { flat := model flag, rules := [], computations := [], conditionLanguage := "en_US",
                          refusals := [] }
    [((readDocument dm (Json.mkObj [("Order", Json.mkObj [("Typo", Json.mkObj [])])])).toOption.map
        (fun read => (read.refusals.length, read.data.groupOccurrences.length))) == some (0, 1),
     ((readDocument dm (Json.mkObj [("Nope", Json.mkObj [])])).toOption.map (·.refusals.length)) == some 0,
     ((readDocument dm (Json.mkObj [("Order", Json.mkObj [("Typo", Json.arr #[])])])).toOption.map
        (·.refusals.length)) == some 1,
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
    (rowInput #[Json.mkObj [("Unknown", .str "x")]]).map (·.refusals.length) = some 0 := by
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

private def temporalPayloadField (typeName : String) (payload : Option Json) : Except String FlatFieldDecl :=
  readFieldType 0 ["Form"] "Value" [] (Json.mkObj [("fieldType", Json.mkObj (
    [("type", .str typeName)] ++ payload.toList.map fun value => (typeName, value)))])

private def temporalField (typeName : String) (format : Option Json) : Except String FlatFieldDecl :=
  temporalPayloadField typeName (some (Json.mkObj (format.toList.map fun value => ("format", value))))

private def temporalProfile (typeName : String) (format : Option Json) : Option (FieldKind × String) := do
  let field ← (temporalField typeName format).toOption
  let policy ← field.temporalTargetPolicy
  pure (field.policy.kind, policy.format)

private def temporalRead (typeName : String) (format : Option Json) (stored : String)
    (zone : String := "UTC") : Option RawCell := do
  let field ← (temporalField typeName format).toOption
  pure (← (classifyStored { fields := [field], timeZoneId := zone } field
    { field := 0, path := [] } stored).toOption).raw

private def defaultClockRead (format : Option Json) : Option (String × RawCell) := do
  let field ← (temporalField "TimeType" format).toOption
  let policy ← field.temporalTargetPolicy
  let cell ← (classifyStored { fields := [field], timeZoneId := "UTC" } field
    { field := 0, path := [] } "12:30:00").toOption
  pure (policy.format, cell.raw)

example : defaultClockRead (some "HH:mm:ss") = some ("HH:mm:ss",
    .parsed (.temporal (.time { epochMillis := 45000000 } { hour := 12, minute := 30, second := 0, valid := by decide }))) := by
  native_decide

example : defaultClockRead none = defaultClockRead (some "HH:mm:ss") := by native_decide

example : [("DateType", "yyyy-MM-dd", FieldKind.temporal .date .fullDate),
    ("TimeType", "HH:mm:ss", .temporal .time .time),
    ("DateTimeType", "yyyy-MM-dd'T'HH:mm:ss", .temporal .dateTime .now)].all
      (fun (typeName, format, kind) =>
        temporalProfile typeName none == some (kind, format) &&
        temporalProfile typeName (some (.str format)) == some (kind, format)) := by native_decide

example : temporalRead "DateType" none "2024-05-06" =
      temporalRead "DateType" (some "yyyy-MM-dd") "2024-05-06" ∧
    (match temporalRead "DateType" none "2024-05-06" with
      | some (.parsed (.temporal (.date value))) => value.parts == { year := 2024, month := 5, day := 6 }
      | _ => false) = true ∧
    temporalRead "DateTimeType" none "2024-05-06T12:30:45" =
      temporalRead "DateTimeType" (some "yyyy-MM-dd'T'HH:mm:ss") "2024-05-06T12:30:45" ∧
    (match temporalRead "DateTimeType" none "2024-05-06T12:30:45" with
      | some (.parsed (.temporal (.dateTime _ date clock _))) =>
          date == { year := 2024, month := 5, day := 6 } &&
          (clock.hour, clock.minute, clock.second) == (12, 30, 45)
      | _ => false) = true := by native_decide

example : temporalProfile "DateType" (some "HH:mm:ss") =
      some (.temporal .date .time, "HH:mm:ss") ∧
    temporalRead "DateType" (some "HH:mm:ss") "12:30:00" =
      (defaultClockRead (some "HH:mm:ss")).map (·.2) := by native_decide

example : !(temporalPayloadField "DateFragmentType" (some (Json.mkObj []))).isOk ∧
    !(temporalField "DateFragmentType" (some "yyyy-MM")).isOk ∧
    ((temporalPayloadField "DateFragmentType" (some (Json.mkObj [("formatOfFragment", "yyyy-MM")]))).toOption.bind
      (·.temporalTargetPolicy) |>.map (·.format)) = some "yyyy-MM" := by native_decide

example : ["DateType", "TimeType", "DateTimeType"].all (fun typeName =>
    [Json.null, .bool true, toJson (1 : Nat), .arr #[], Json.mkObj []].all
      (fun value => !(temporalField typeName (some value)).isOk) &&
    [none, some Json.null, some (.str "yyyy-MM-dd"), some (.bool true),
      some (toJson (1 : Nat)), some (.arr #[])].all
      (fun payload => !(temporalPayloadField typeName payload).isOk)) := by native_decide

example : temporalRead "DateType" none "2024-02-30" = some (.rejected .dateFormat) ∧
    temporalRead "DateType" none "1500-01-01" = some (.rejected .dateInvalid) ∧
    temporalRead "DateType" (some "yyyy-MM-dd") "2024-02-30" = some (.rejected .dateFormat) ∧
    temporalRead "DateType" (some "yyyy-MM-dd") "1500-01-01" = some (.rejected .dateInvalid) ∧
    temporalRead "DateType" (some "yyyy-MM-dd") "2024-05-06" "unsupported-zone" = none := by native_decide

/-- A one-field model whose Number body is `body`, returning the reader's refusals of that field. -/
private def numberBodyRefusals (body : List (String × Json)) : Option (List String) :=
  let field := Json.mkObj [("type", "Field"), ("name", "N"), ("Field", Json.mkObj [("fieldType",
    Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj body)])])]
  let group := Json.mkObj [("type", "Group"), ("name", "G"),
    ("Group", Json.mkObj [("repeatability", (1 : Nat)), ("elements", Json.arr #[field])])]
  let json := Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group])])])]
  (readModel json).toOption.map fun model => model.refusals.map (·.2)

/-- The resolved scale, minimum fractional count and whether stored text meets the fractional arms,
for the one field of a model whose Number body is `body`. -/
private def numberBodyFractional (body : List (String × Json)) : Option (Nat × Nat × Bool) := do
  let field := Json.mkObj [("type", "Field"), ("name", "N"), ("Field", Json.mkObj [("fieldType",
    Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj body)])])]
  let group := Json.mkObj [("type", "Group"), ("name", "G"),
    ("Group", Json.mkObj [("repeatability", (1 : Nat)), ("elements", Json.arr #[field])])]
  let json := Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group])])])]
  let model ← (readModel json).toOption
  let declaration ← model.flat.fields.head?
  let .number info := declaration.policy.kind | none
  pure (info.scale, declaration.numericTargetConstraints.minFractionalDigits,
    declaration.numericTargetConstraints.fractionalDigitsChecked)

/- The no-bound sentinel `-1` is not an absent member: it resolves into an ordinary pair, a `-1`
maximum fixing the count at the minimum, except that a `-1` minimum beside a zero maximum leaves the
fractional arms unchecked; both written `-1` is refused (rows `s-*` of the `model-consistency` and
the stored rows of the `number-declaration-bounds` capture). -/
example :
    numberBodyFractional [("minFractionalDigits", (-1 : Int)), ("maxFractionalDigits", (2 : Nat))] =
        some (2, 0, true) ∧
      numberBodyFractional [("maxFractionalDigits", (-1 : Int)), ("minFractionalDigits", (1 : Nat))] =
        some (1, 1, true) ∧
      numberBodyFractional [("maxFractionalDigits", (-1 : Int))] = some (0, 0, true) ∧
      numberBodyFractional [("minFractionalDigits", (-1 : Int))] = some (0, 0, false) ∧
      numberBodyFractional [("minFractionalDigits", (-1 : Int)), ("maxFractionalDigits", (-1 : Int))] = none ∧
      numberBodyRefusals [("minFractionalDigits", (-1 : Int)), ("maxFractionalDigits", (-1 : Int))] =
        some ["MVK_FRACT_DIGITS_MISSING"] ∧
      numberBodyRefusals [("maxFractionalDigits", (2 : Nat)), ("minFractionalDigits", (1 : Nat))] =
        some [] := by
  native_decide

end A12Kernel.Dm.ReaderLocks
