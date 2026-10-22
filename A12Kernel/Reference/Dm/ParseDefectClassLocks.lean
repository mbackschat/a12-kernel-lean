import A12Kernel.Reference.Dm.ParseDefectClass
import A12Kernel.Reference.Dm.HavingAdmission

/-! # Locks for the first class beside a parse defect

The model is the declaration-report capture's form: `Form` with String fields `Value` and `Other`, the
rule declared in `Form`
([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14)).
-/

namespace A12Kernel.Dm.ParseDefectClassLocks

open A12Kernel

private def model : FlatModel :=
  { fields := [{ id := 0, groupPath := ["Form"], name := "Value", policy := { kind := .string } },
      { id := 1, groupPath := ["Form"], name := "Other", policy := { kind := .string } }] }

private def classOf (text : String) : Option String := parseDefectClass? model ["Form"] .english text

/- `r-two-defects-name-first` reports the name and `r-two-defects-token-first` the token; the
sound-name twin keeps the token, and an unresolved name after the defect does not displace it. A
text that parses is lowering's question, and so is `c-pre-bad-op-token`'s operation alone. -/
example :
    classOf "FieldFilled(Nope) And And FieldFilled(Value)" = some "MVK_INVALID_ENTITY" ∧
    classOf "FieldFilled(Value) And And FieldFilled(Nope)" = some "MVK_UNEXPECTED_TOKEN" ∧
    classOf "FieldFilled(Value) And And FieldFilled(Value)" = some "MVK_UNEXPECTED_TOKEN" ∧
    classOf "FieldFilled(Value) And FieldFilled(Other) And And FieldFilled(Nope)" =
      some "MVK_UNEXPECTED_TOKEN" ∧
    classOf "FieldFilled(Nope)" = none ∧
    classOf "1 + + 1" = some "MVK_UNEXPECTED_TOKEN" := by
  native_decide

/-- The spec's production-close and walked-path rows (spec/12 §12.3), read on a form with String
`Reference` and `Code` and a repeatable `Items` holding a Number `Count`. -/
private def spec12 : FlatModel :=
  { fields := [{ id := 0, groupPath := ["Form"], name := "Reference", policy := { kind := .string } },
      { id := 1, groupPath := ["Form"], name := "Code", policy := { kind := .string } },
      { id := 2, groupPath := ["Form", "Items"], name := "Count", policy := { kind := .number { scale := 0, signed := true } },
        repeatableScope := [1] }]
    repeatableGroups := [{ level := 1, path := ["Form", "Items"], repeatability := some 5 }] }

private def spec12Class (text : String) (group : GroupPath := ["Form"]) : Option String :=
  parseDefectClass? spec12 group .english text

/- A reference is checked once its path closes, and a walked path's completed steps are checked even
when it never closes; an unwalked open path, a resolving walked prefix and a step stopped inside draw
the token class. -/
example :
    spec12Class "FieldFilled(NoSuch Code)" = some "MVK_INVALID_ENTITY" ∧
    spec12Class "FieldFilled(NoSuch/)" = some "MVK_UNEXPECTED_TOKEN" ∧
    spec12Class "FieldFilled(Reference) NoSuchField" = some "MVK_UNEXPECTED_TOKEN" ∧
    spec12Class "FieldFilled(Items*/NoSuch/)" = some "MVK_INVALID_ENTITY" ∧
    spec12Class "FieldFilled(NoSuch/Items*/)" = some "MVK_INVALID_ENTITY" ∧
    spec12Class "FieldFilled(../NoSuch/)" ["Form", "Items"] = some "MVK_INVALID_ENTITY" ∧
    spec12Class "FieldFilled(/NoRoot/Items*/)" = some "MVK_INVALID_ROOT_GROUP" ∧
    spec12Class "FieldFilled(Items/NoSuch/)" = some "MVK_UNEXPECTED_TOKEN" ∧
    spec12Class "FieldFilled(/NoRoot/)" = some "MVK_UNEXPECTED_TOKEN" ∧
    spec12Class "FieldFilled(Items*/Count/)" = some "MVK_UNEXPECTED_TOKEN" ∧
    spec12Class "FieldFilled(Items*/NoSuch.)" = some "MVK_UNEXPECTED_TOKEN" := by
  native_decide

/- A `.*` step is walked before its own class is raised: a step naming nothing draws the name's class,
a resolving one `MVK_POINT_IN_A12_MODEL` (spec/12 §12.3); the plain star is the admitted twin. -/
example :
    spec12Class "FieldFilled(Items.*/Count)" = some "MVK_POINT_IN_A12_MODEL" ∧
    spec12Class "FieldFilled(NoSuch.*/Items/)" = some "MVK_INVALID_ENTITY" ∧
    spec12Class "FieldFilled(Items*/Count)" = none := by
  native_decide

/-- The class ordered admission raises for a whole condition on a form with String `Reference` and
Number `Score`, `none` when it admits it. -/
private def admissionClass (text : String) : Option String :=
  let form : FlatModel :=
    { fields := [{ id := 0, groupPath := ["Form"], name := "Reference", policy := { kind := .string } },
        { id := 1, groupPath := ["Form"], name := "Score", policy := { kind := .number { scale := 0, signed := true } } }] }
  match parseText .english text with
  | .error error => some error.errorClass.code
  | .ok parsed => match checkOrderedAdmission form ["Form"] ["Form"] parsed.body with
    | .ok () => none
    | .error refusal => some refusal.detail

/- A comparison standing as an operation's operand is a token defect, after the operand read before it
keeps its own production's check (spec/12 §12.3); the rounding twins separate the gate from the token,
and the connective is this account's extension of the comparison rows. -/
example :
    admissionClass "Abs(RoundUpValue(Reference, 2) > 1) > 0" = some "MVK_NO_NUMBER" ∧
    admissionClass "Abs(RoundUpValue(Score, 2) > 1) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    admissionClass "Max([Score] > 1, 2) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    admissionClass "Abs([Score] > 1 And [Score] > 2) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    admissionClass "Abs(RoundUpValue(Score, 2)) > 0" = none := by
  native_decide

/-- The first class of a whole condition on a form with String `Reference`, Number `Score` and Date
`Due`: the parse-defect producer's for a text that does not parse, ordered admission's otherwise. -/
private def firstClass (text : String) : Option String :=
  let form : FlatModel :=
    { fields := [{ id := 0, groupPath := ["Form"], name := "Reference", policy := { kind := .string } },
        { id := 1, groupPath := ["Form"], name := "Score", policy := { kind := .number { scale := 0, signed := true } } },
        { id := 2, groupPath := ["Form"], name := "Due",
          policy := { kind := .temporal .date .fullDate } }] }
  match parseDefectClass? form ["Form"] .english text with
  | some code => some code
  | none => match parseText .english text with
    | .error error => some error.errorClass.code
    | .ok parsed => match checkOrderedAdmission form ["Form"] ["Form"] parsed.body with
      | .ok () => none
      | .error refusal => some refusal.detail

/- A condition call in an operation position is a token defect at its own position, after the checks
of every production completed before it: a predicate as an operation's operand, inside arithmetic or
as a comparison side, its own read unchecked (`q02`); a rounding or date operand completed first keeps
its class (`q05`, `t03`, `t06`, `d01`, `d05`), and a date slot's gate also precedes a connective
defect (`d03`, `d06`, `d09`) where a sound date read does not (`d04`). Rows of the predicate-operand
capture, 2026-10-14. -/
example :
    firstClass "Abs(FieldFilled(Score)) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(FieldFilled(NoSuch)) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Max(FieldFilled(Score), 2) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(RoundUpValue(Reference, 2) + FieldFilled(Score)) > 0" = some "MVK_NO_NUMBER" ∧
    firstClass "Abs(RoundUpValue(Score, 2) + FieldFilled(Score)) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(FieldValueIncludedInValueList(Reference, \"a\")) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(GroupFilled(/Form)) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "[Score] + FieldFilled(Score) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "FieldFilled(Score) + 1 > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "RoundUpValue(Reference, 2) + FieldFilled(Score) > 0" = some "MVK_NO_NUMBER" ∧
    firstClass "FieldFilled(Score) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "[Score] > FieldFilled(Score)" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "RoundUpValue(Reference, 2) > FieldFilled(Score)" = some "MVK_NO_NUMBER" := by
  native_decide

-- A name that is no keyword before `(` fails at the name, unresolved: `Year` is no operator, so
-- `Reference` and `Due` alike draw the token class (rows `d01`–`d05` of the first predicate-operand
-- file), where a resolution-first account would report the unknown `Year` as an entity.
example :
    firstClass "Abs(Year(Reference) > 1) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(Year(Due) > 1) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(Year(Reference)) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(Year(Reference) + FieldFilled(Score)) > 0" = some "MVK_UNEXPECTED_TOKEN" := by
  native_decide

example :
    firstClass "Abs(YearFromDate(Reference) > 1) > 0" = some "MVK_NO_DATE" ∧
    firstClass "Abs(YearFromDate(Due) > 1) > 0" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "YearFromDate(Reference) > 1 And And FieldFilled(Score)" = some "MVK_NO_DATE" ∧
    firstClass "YearFromDate(Due) > 1 And And FieldFilled(Score)" = some "MVK_UNEXPECTED_TOKEN" ∧
    firstClass "Abs(YearFromDate(Reference) + FieldFilled(Score)) > 0" = some "MVK_NO_DATE" ∧
    firstClass "AddDays(Reference, 1) > Today And And FieldFilled(Score)" = some "MVK_NO_DATE" ∧
    firstClass "FieldFilled(Due) And YearFromDate(Reference) > 1 And And FieldFilled(Score)" =
      some "MVK_NO_DATE" := by
  native_decide

end A12Kernel.Dm.ParseDefectClassLocks
