import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # How the DM-JSON readers bind non-text members, and how a date constant is typed

Each expectation is a Kernel row the a12-dmkits handbacks of 2026-10-18, 2026-10-21 and 2026-10-22
retain ([October 18](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18),
[October 21](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21),
[October 22](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-22)). A model the Kernel
does not build is a read error or a refused declaration here; neither is a Kernel class. Each model is
written as text and parsed as the readers parse a model file. -/

namespace A12Kernel.Dm.MemberBindingLocks

open Lean A12Kernel

private def model (fieldMembers typeBody : String) (typeName : String := "StringType")
    (groupMembers : String := "") (info : String := "{}") (config : String := "{}")
    (definitions : String := "[]") : Json :=
  (parseModelJson s!"\{\"content\":\{\"modelInfo\":{info},\"modelConfig\":{config},\"typeDefinitions\":{definitions},\"modelRoot\":\{\"rootGroups\":[\{\"type\":\"Group\",\"name\":\"Form\",\"Group\":\{\"elements\":[\{\"type\":\"Group\",\"name\":\"Rows\",\"Group\":\{{groupMembers}\"elements\":[\{\"type\":\"Field\",\"name\":\"Value\",\"Field\":\{{fieldMembers}\"fieldType\":\{\"type\":\"{typeName}\",\"{typeName}\":{typeBody}}}}]}}]}}]}}}").toOption.getD .null

/-- The read model, or `none` when the read fails or refuses a declaration. -/
private def built? (json : Json) : Option DmModel :=
  match readModel json with
  | .ok read => if read.refusals.isEmpty then some read else none
  | .error _ => none

private def field? (json : Json) : Option FlatFieldDecl :=
  (built? json).bind (·.flat.fields.head?)

private def refusalCodes (json : Json) : List String :=
  match readModel json with
  | .ok read => read.refusals.map (·.2)
  | .error _ => []

/-- `noValueValidation`, written as the member's JSON value. -/
private def rawString (written : String) : Option Bool :=
  (field? (model "" s!"\{\"lineBreaksPermitted\":true,\"noValueValidation\":{written}}")).map
    (·.stringValueMode == .raw)

/-- The boolean law, measured on `noValueValidation` and `fieldRefByShortNameAllowed`: Java's `trim`,
then six spellings; the text `null` and a blank text are the default; an integer is set unless zero. -/
example :
    ["true", "\"true\"", "\"True\"", "\"TRUE\"", "\" true\"", "\"\\ttrue\"", "\"true\\n\"", "\" TRUE\"",
      "1", "2", "-1", "12345678901234567890123456"].all (rawString · == some true) ∧
    ["false", "\"false\"", "\"False\"", "\"FALSE\"", "\"\"", "\" \"", "\"null\"", "\" null\"", "0", "null"].all
      (rawString · == some false) ∧
    ["\"tRUE\"", "\"FaLsE\"", "\"NULL\"", "\"yes\"", "\"1\"", "\"\\u00A0true\"", "\"\\u2003true\"", "0.5",
      "1.5", "1.0", "{}", "[]"].all (rawString · == none) := by
  native_decide

/-- A boolean member reads a number token by its kind: an integer is set unless zero, `-0` clearing, and
a fraction or an exponent is refused even where it is worth one or zero. -/
example :
    rawString "-0" = some false ∧
    ["1e0", "1E+0", "0e0", "1.0e1", "0.1e1", "10e-1", "1e1", "-0.0"].all (rawString · == none) ∧
    field? (model "" "{\"positivesOnly\":1e0}" "NumberType") = none ∧
    field? (model "" "{\"youngerThan1900Check\":1E+0}" "DateType") = none ∧
    field? (model "\"global\":1e0," "{}") = none ∧
    (field? (model "\"global\":-0," "{}")).map (·.isGlobal) = some false ∧
    ["1", "0", "-0"].all (fun written =>
      (built? (model "" "{}" (info := s!"\{\"immutable\":{written},\"metaData\":{written}}"))).isSome &&
        (built? (model "" "{}" (config := s!"\{\"fieldRefByShortNameAllowed\":{written}}"))).isSome) ∧
    ["1e0", "0e0", "1.0e1", "0.1e1", "1.0", "1e1", "10e-1", "-0.0"].all (fun written =>
      (built? (model "" "{}" (info := s!"\{\"immutable\":{written}}"))).isNone &&
        (built? (model "" "{}" (info := s!"\{\"metaData\":{written}}"))).isNone &&
        (built? (model "" "{}" (config := s!"\{\"fieldRefByShortNameAllowed\":{written}}"))).isNone) := by
  native_decide

private def signed? (written : String) : Option Bool :=
  match field? (model "" s!"\{\"positivesOnly\":{written}}" "NumberType") with
  | some { policy := { kind := .number info }, .. } => some info.signed
  | _ => none

/-- Every primitive boolean member binds by the same law, a field the variant filter deletes included,
and a type definition no field references too. -/
example :
    signed? "\" TRUE\"" = some false ∧ signed? "\"tRUE\"" = none ∧ signed? "1.5" = none ∧
    (field? (model "\"global\":\" TRUE\"," "{}")).map (·.isGlobal) = some true ∧
    field? (model "\"global\":\"yes\"," "{}") = none ∧
    field? (model "\"transient\":\"tRUE\"," "{}") = none ∧
    field? (model "" "{\"alphabeticalSorting\":1.5}") = none ∧
    field? (model "" "{\"zeroNotAllowed\":\"tRUE\"}" "NumberType") = none ∧
    field? (model "" "{\"leadingZerosAllowed\":\"tRUE\"}" "NumberType") = none ∧
    field? (model "" "{\"youngerThan1900Check\":\"tRUE\"}" "DateType") = none ∧
    field? (model "\"variantFilter\":{\"filterType\":\"ONLY\",\"variants\":[\"other\"]},"
      "{\"lineBreaksPermitted\":\"tRUE\"}") = none ∧
    built? (model "" "{}" (definitions :=
      "[{\"id\":\"T\",\"fieldType\":{\"type\":\"NumberType\",\"NumberType\":{\"positivesOnly\":\"tRUE\"}}}]")) = none ∧
    built? (model "" "{}" (info := "{\"immutable\":1.5}")) = none ∧
    built? (model "" "{}" (info := "{\"metaData\":\"tRUE\"}")) = none ∧
    (built? (model "" "{}" (config := "{\"fieldRefByShortNameAllowed\":\" TRUE\"}"))).map
      (·.flat.fieldRefByShortNameAllowed) = some true ∧
    built? (model "" "{}" (config := "{\"fieldRefByShortNameAllowed\":\"tRUE\"}")) = none := by
  native_decide

private def count? (written : String) : Option (Option Nat) :=
  (built? (model "" "{}" (groupMembers := s!"\"repeatability\":{written},"))).map fun read =>
    read.flat.repeatableGroups.head?.bind (·.repeatability)

/-- A count binds through `Integer.parseInt` after `trim`, a JSON number truncated toward zero inside
the `int` range; a count below one, `null` and its text are `MVK_MAX_VALUES_INVALID`. -/
example :
    ["3", "\"3\"", "\" 3 \"", "\"\\t3\\n\"", "\"+3\"", "\"03\"", "\"\\u0663\"", "\"\\uFF13\"", "3.7"].all
      (count? · == some (some 3)) ∧
    count? "1e1" = some (some 10) ∧
    ["\"3.7\"", "\"1e1\"", "\"0x3\"", "\"\\u00A03\"", "\"3\\u00A0\"", "\"99999999999\"", "2147483648",
      "3e10", "true", "{}", "[]", "\"NULL\"", "2147483647.5"].all (count? · == none) ∧
    ["0", "-1", "\"-1\"", "-3.7", "\"\"", "null", "\"null\"", "\" null \""].all fun written =>
      refusalCodes (model "" "{}" (groupMembers := s!"\"repeatability\":{written},")) ==
        ["MVK_MAX_VALUES_INVALID"] := by
  native_decide

private def baseYear? (written : String) : Option (Option Int) :=
  (built? (model "" "{}" (info := s!"\{\"baseYear\":{written}}"))).map (·.flat.baseYear)

/-- The base year binds by the same integer law; a blank text and the text `null` are no year. -/
example :
    ["\"2024\"", "\" 2024 \"", "\"\\u0662\\u0660\\u0662\\u0664\"", "2024", "2024.7"].all
      (baseYear? · == some (some 2024)) ∧
    baseYear? "2147483647.0" = some (some 2147483647) ∧
    ["\"\"", "\"  \"", "\"null\"", "\" null \"", "null"].all (baseYear? · == some none) ∧
    ["\"\\u00A02024\"", "\"2024.0\"", "\"x\"", "\"NULL\"", "\"Null\"", "\"2147483648\"", "2147483648",
      "-2147483649", "2147483647.5", "{}", "[2024]", "true"].all (baseYear? · == none) := by
  native_decide

/-- An `int` member reads a number alike in its plain and its exponent spelling. -/
example :
    ["1e1", "10.0"].all (count? · == some (some 10)) ∧
    ["1.0E9", "1000000000.0"].all (count? · == some (some 1000000000)) ∧
    ["2147483647.0", "2.147483647E9"].all (count? · == some (some 2147483647)) ∧
    ["3e10", "3.0E10", "2147483647.5", "2.1474836475E9", "-2147483648.5", "-2.1474836485E9",
      "2147483648.0", "2.147483648E9", "-2147483649.0", "-2.147483649E9"].all (count? · == none) ∧
    ["2147483647.0", "2.147483647E9"].all (baseYear? · == some (some 2147483647)) ∧
    ["2147483647.5", "2.1474836475E9", "-2147483648.5", "-2.1474836485E9", "2147483648.0",
      "2.147483648E9"].all (baseYear? · == none) := by
  native_decide

/- The respelling keeps each token's value and gives an exponent token a fraction digit; a string is
untouched, and an exponent past the represented bound refuses the model before any power is taken, as
an `int` read bounds its power by the mantissa's digits. -/
example :
    ((parseModelJson "[1e0,-0,1.5e-2,0E5,10E+2,\"1e0\"]").toOption ==
      (Json.parse "[1.0,0,0.015,0.0,1000.0,\"1e0\"]").toOption) = true ∧
    (parseModelJson "{\"a\":1e1000000000}").isOk = false ∧
    (parseModelJson "{\"a\":1e-1000000000}").isOk = false ∧
    (parseModelJson "[01e1]").isOk = false ∧ (parseModelJson "[1.e1]").isOk = false ∧
    (intMember? (Json.mkObj [("k", .num { mantissa := 5, exponent := 1000000000 })]) "k").toOption =
      some (some 0) := by
  native_decide

/-- The text `null` is no Number bound. -/
example :
    (field? (model "" "{\"minValue\":\"null\"}" "NumberType")).map
      (·.numericTargetConstraints.minimum) = some none := by
  native_decide

private def booleanCell (stored : String) : String :=
  let declaration : FlatFieldDecl := { id := 0, groupPath := ["Form"], name := "B", policy := { kind := .boolean } }
  match classifyStored { fields := [declaration] } declaration { field := 0, path := [] } stored with
  | .ok { raw := .parsed (.bool value), .. } => toString value
  | .ok { raw := .rejected .booleanToken, .. } => "token"
  | _ => "other"

/-- A Boolean cell is compared with Java's `equalsIgnoreCase`, which folds the long s onto `s`; the dotted
capital I and the Kelvin sign fold onto letters neither word holds, so alone each is the long s's token
class. -/
example :
    ["true", "TRUE", "tRuE"].all (booleanCell · == "true") ∧
    ["fal\u017Fe", "FAL\u017FE"].all (booleanCell · == "false") ∧
    ["\u017F", "\u0130", "\u212A"].all (booleanCell · == "token") := by
  native_decide

private def builtYear : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Built",
    policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy") },
    temporalTargetPolicy := some { format := "yyyy" } }

/-- A stored year reads ASCII digits only: Arabic-Indic and fullwidth digits are a date-format error
(2026-10-21 §1.14). -/
example :
    ["\u0661\u0669\u0666\u0663", "\uFF11\uFF19\uFF16\uFF13"].all (fun stored =>
      match classifyStored { fields := [builtYear] } builtYear { field := 0, path := [] } stored with
      | .ok { raw := .rejected .dateFormat, .. } => true
      | _ => false) &&
    (match classifyStored { fields := [builtYear] } builtYear { field := 0, path := [] } "1963" with
      | .ok { raw := .parsed _, .. } => true
      | _ => false) = true := by
  native_decide

/-- A `DD.MM.YYYY` constant is real on the hybrid calendar: the ten cutover labels are text and a
Julian leap day is a date, which the proleptic value carrier cannot hold and so leaves unvalued. A
date-time constant is typed by the same calendar, and one before the value floor stays unvalued. -/
example :
    ["04.10.1582", "15.10.1582"].all (civilDateConstant? · |>.isSome) ∧
    ["05.10.1582", "14.10.1582", "29.02.1700"].all (!isTemporalConstant ·) ∧
    ["29.02.1500", "29.02.1300"].all isTemporalConstant ∧
    ["29.02.1500", "29.02.1300"].all (civilDateConstant? · |>.isNone) ∧
    !isTemporalConstant "05.10.1582T00:00:00" ∧ isTemporalConstant "04.10.1582T23:00:00" ∧
    (dateTimeConstant? "04.10.1582T23:00:00").isNone := by
  native_decide

end A12Kernel.Dm.MemberBindingLocks
