import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.TemporalReferenceAdmissionLocks

private def model : FlatModel := {
  timeZoneId := "Europe/Berlin"
  fields := [
    { id := 1, groupPath := ["Form", "Rows"], name := "N", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form", "Rows"], name := "M", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Due", repeatableScope := [10], policy := { kind := .temporal .date TemporalComponents.fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 4, groupPath := ["Form", "Rows"], name := "Stamp", repeatableScope := [10], policy := { kind := .temporal .dateTime TemporalComponents.now }, temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def references (condition : String) (field : FieldId := 1) (level : RepeatableLevel := 10)
    (errorPath : String := "Rows/N") (fixture : FlatModel := model) : Option (Option Bool × Option Bool × Option Bool) := do
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Recursive", errorCode := "RECURSIVE", errorEntityRelPath := "../" ++ errorPath,
    condition, severity := "ERROR" }).toOption
  pure (rule.condition.core.authoredErrorReference? field, rule.condition.core.formOnlyErrorReference? field,
    rule.condition.core.errorReferenceAt? field level)

private def conditions := [
  "DayFromDate(AddDays(Rows/Due,[Rows/N])) > 0",
  "HoursFromTime(AddHours(Rows/Stamp,[Rows/N])) > 0",
  "DayFromDate(AddDays(Rows/Due,Sum(Rows/N,Rows/M))) > 0",
  "DayFromDate(AddDays(Rows/Due,FirstFilledValue(Rows/N,Rows/M))) > 0",
  "DayFromDate(AddDays(Rows/Due,NumberOfFilledFields(Rows/N,Rows/M))) > 0",
  "DayFromDate(AddDays(Rows/Due,DayFromDate(AddDays(Rows/Due,[Rows/N])))) > 0"]

example : model.validate.isOk = true := by native_decide
example : conditions.all (fun condition =>
    references condition == some (some true, some false, some true)) = true := by native_decide

example : conditions.all (fun condition =>
    references condition 99 == some (some false, some false, some false) &&
    references condition 1 20 == some (some true, some false, some false) &&
    references ("GroupFilled(/Form) And " ++ condition) == some (some true, some false, some true)) = true := by native_decide

example : ["DayFromDate(AddDays(Rows/Due,[Rows/M])) > 0",
    "HoursFromTime(AddHours(Rows/Stamp,[Rows/M])) > 0"].all
    (fun condition => (references condition).isNone &&
      references condition 2 10 "Rows/M" == some (some true, some false, some true)) = true := by native_decide

example : references "DayFromDate(AddDays(Rows/Due,[Rows/N])) > 0" 2 =
    some (some false, some false, some false) ∧
    references "DayFromDate(AddDays(Rows/Due,Sum(Rows/N,Rows/M))) > 0" 2 =
    some (some true, some false, some true) := by native_decide

private def rootDate : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with groupPath := ["Form"], repeatableScope := [] } else field }

example : rootDate.validate.isOk = true ∧
    references "DayFromDate(AddDays(Due,[Rows/N])) > 0" 1 10 "Rows/N" rootDate =
      some (some true, some false, some true) := by native_decide

end A12Kernel.Dm.TemporalReferenceAdmissionLocks
