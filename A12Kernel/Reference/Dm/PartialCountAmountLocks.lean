import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Replay

/-! # Count shift amounts under partial validation and typed direct lists at the rule's row

A count inside a shift amount answers a partial call as the same count does as a comparison operand:
a value count takes declared-slot coverage, a filled-field count the all-rows gate and
`NumberOfFilledGroups` its four-step instance walk. Typed direct lists in a rule bound to a repeatable
row read that row, in full and partial validation. Each expectation is the Kernel's outcome in the
[K22 count-amount checkpoint](../../../docs/sources/group-count-topology.md#src-k22-runtime-r11), whose
capture the population replay also compares row by row; these locks keep the separating rows in the
build.
-/

namespace A12Kernel.Dm.PartialCountAmountLocks
open A12Kernel A12Kernel.Dm Lean

private def field (name : String) (fieldType : Json) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name), ("Field", Json.mkObj [("fieldType", fieldType)])]

private def typed (kind : String) (body : List (String × Json) := []) : Json :=
  Json.mkObj [("type", Json.str kind), (kind, Json.mkObj body)]

private def date : Json := typed "DateType" [("format", "yyyy-MM-dd")]
private def time : Json := typed "TimeType" [("format", "HH:mm:ss")]

private def rule (name target condition : String) : Json :=
  Json.mkObj [("type", "Rule"), ("name", Json.str name), ("Rule", Json.mkObj [
    ("errorEntityRelPath", Json.str target), ("errorCode", Json.str name), ("errorCondition", Json.str condition),
    ("severity", "ERROR"), ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "probe")]])])]

private def group (name : String) (repeatability : Nat) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name),
    ("Group", Json.mkObj [("repeatability", toJson repeatability), ("elements", Json.arr elements.toArray)])]

private def modelOf (form : List Json) : Json :=
  Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("timeZone", "Europe/Berlin"),
        ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group "Form" 1 form])])])]

private def world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }

/-- Every rule's firings as `code@pointer`, sorted: full validation without `relevant`, otherwise one
partial call over it. -/
private def firings (modelJson document : Json) (relevant : Option (List RelevantEntityPattern) := none) :
    Option (List String) := do
  let model ← (readModel modelJson).toOption
  let input ← (readDocument model document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let fired ← (validationRules model .english).mapM fun dmRule => do
    let checkedRule ← (checkValidationRule model .english dmRule world).toOption
    let messages ← (match relevant with
      | none => runValidationRule world validated checkedRule
      | some relevant => runRulePartial world checked relevant checkedRule).toOption
    pure (messages.map fun message => let observed := observe model.flat message
      s!"{observed.code}@{observed.pointer}")
  pure (fired.flatten.mergeSort (· ≤ ·))

private def every (path : List String) : RelevantEntityPattern := RelevantEntityPattern.allInstances path

private def at_ (path : List String) (indices : List Nat) : RelevantEntityPattern :=
  { path, indices := indices.map fun n => if n == 0 then .all else .concrete n }

/-! ## Count shift amounts beside a comparison twin

`Rows` holds two declared rows, so the two concrete group rows cover its whole capacity, the shape of
the checkpoint's `NWild-g123` row. -/

private def shift (amount : String) : String := s!"FieldFilled(Ref) And (AddDays(Low, {amount}) != \"01.01.1900\")"

private def countModel : Json := modelOf [
  field "Ref" (typed "StringType"), field "Low" date,
  group "Rows" 2 [field "N" (typed "NumberType" [("maxFractionalDigits", toJson (0 : Nat))]),
    field "S" (typed "StringType")],
  rule "SV1" "../Ref" (shift "NumberOfValueInFields(3 In Rows*/N)"),
  rule "SC5" "../Ref" (shift "NumberOfFilledFields(Rows*/N)"),
  rule "SG3" "../Ref" (shift "NumberOfFilledGroups(Rows*)"),
  rule "CV2" "../Ref" "FieldFilled(Ref) And (NumberOfValueInFields(\"1\" In Rows*/S) >= 0)"]

private def countDocument (first : String) : Json :=
  Json.mkObj [("Form", Json.mkObj [("Ref", "x"), ("Low", "2024-03-01"), ("Rows", Json.arr #[
    Json.mkObj [("N", Json.str first), ("S", "1")],
    Json.mkObj [("N", "1"), ("S", "2")]])])]

private def countCall (first : String) (extra : List RelevantEntityPattern) : Option (List String) :=
  firings countModel (countDocument first) (some ([every ["Form", "Ref"], every ["Form", "Low"]] ++ extra))

private def groupRows : List RelevantEntityPattern := [at_ ["Form", "Rows"] [1, 1], at_ ["Form", "Rows"] [1, 2]]

/-- The column wildcard alone: the value and filled-field counts pass, and the group count, whose
first instance is not fully relevant, does not. -/
example : countCall "3" [at_ ["Form", "Rows", "N"] [1, 0, 1]] = some ["SC5@Form/Ref", "SV1@Form/Ref"] := by
  native_decide

/-- Concrete group rows beside the wildcard pass the value count and the group walk but cancel the
filled-field count's all-rows gate, and they cover `S` for the String value count without a
wildcard (`SV1`, `SG3`, `CV2` against `SC5`). -/
example : countCall "3" (at_ ["Form", "Rows", "N"] [1, 0, 1] :: groupRows) =
    some ["CV2@Form/Ref", "SG3@Form/Ref", "SV1@Form/Ref"] := by native_decide

/-- A malformed first instance leaves the group walk, the filled-field count and the Number value
count unavailable, while the String count over clean cells still answers. -/
example : countCall "x" [at_ ["Form", "Rows"] [1, 0]] = some ["CV2@Form/Ref"] := by native_decide

/-- The group wildcard alone covers every count. -/
example : countCall "3" [at_ ["Form", "Rows"] [1, 0]] =
    some ["CV2@Form/Ref", "SC5@Form/Ref", "SG3@Form/Ref", "SV1@Form/Ref"] := by native_decide

/-! ## Typed direct lists in a row-bound rule -/

private def rowRule (name condition : String) : Json := rule name "../E" s!"FieldFilled(E) And ({condition})"

private def rowModel : Json := modelOf [
  field "RB1" (typed "BooleanType"), field "RB2" (typed "BooleanType"),
  group "Rows" 3 [field "D1" date, field "D2" date, field "T1" time, field "T2" time,
    field "B1" (typed "BooleanType"), field "B2" (typed "BooleanType"), field "E" (typed "StringType"),
    rowRule "L06" "NumberOfDifferentValues(T1, T2) == 1",
    rowRule "L07" "NumberOfValueInFields(True In B1, B2) == 2",
    rowRule "L10" "NumberOfDifferentValues(D1, D2) == 1",
    rowRule "L13" "FieldValuesNotUnique(D1, D2)",
    rowRule "L14" "NumberOfValueInFields(True In /Form/RB1, /Form/RB2) == 2"]]

private def rowDocument : Json :=
  Json.mkObj [("Form", Json.mkObj [("RB1", "true"), ("RB2", "true"), ("Rows", Json.arr #[
    Json.mkObj [("D1", "2024-01-01"), ("D2", "2024-02-01"), ("T1", "01:00:00"), ("T2", "01:00:00"),
      ("B1", "true"), ("B2", "true"), ("E", "x")],
    Json.mkObj [("D1", "2024-03-01"), ("D2", "2024-03-01"), ("T1", "01:00:00"), ("T2", "02:00:00"),
      ("B1", "true"), ("B2", "false"), ("E", "x")]])])]

private def rowCall (fields : List String) : Option (List String) :=
  firings rowModel rowDocument (some ((("E" :: fields).map fun name => at_ ["Form", "Rows", name] [1, 0, 1])))

/-- Each list reads the rule's own row: the rows differ on every operator, and the root Boolean pair
holds on both. -/
example : firings rowModel rowDocument = some ["L06@Form/Rows/E", "L07@Form/Rows/E", "L10@Form/Rows[2]/E",
    "L13@Form/Rows[2]/E", "L14@Form/Rows/E", "L14@Form/Rows[2]/E"] := by native_decide

/-- A partial call needs both operands relevant at the row. -/
example : rowCall ["B1", "B2"] = some ["L07@Form/Rows/E"] ∧ rowCall ["B1"] = some [] ∧
    rowCall ["D1", "D2"] = some ["L10@Form/Rows[2]/E", "L13@Form/Rows[2]/E"] ∧ rowCall ["D1"] = some [] := by
  native_decide

end A12Kernel.Dm.PartialCountAmountLocks
