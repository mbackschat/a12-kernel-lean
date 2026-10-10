import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.SelectedReferenceAdmissionLocks

private def model : FlatModel := {
  fields := [
    { id := 8, groupPath := ["Form", "Rows"], name := "Out", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 1, groupPath := ["Form"], name := "Key", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "Fallback", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Code", repeatableScope := [10], policy := { kind := .string } },
    { id := 4, groupPath := ["Form", "Rows", "Body"], name := "N", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, groupPath := ["Form", "Rows", "Body"], name := "M", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 6, groupPath := ["Form", "Rows"], name := "Other", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def admission (condition : String) (error : String := "Rows/Body/N") (fixture : FlatModel := model) : String :=
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED",
    errorEntityRelPath := "../" ++ error, condition, severity := "ERROR" } with
  | .ok _ => "admitted"
  | .error refusal =>
      if refusal.detail.startsWith "A12Kernel.FlatRuleAssemblyError.errorFieldIterationInvalid" then "iteration"
      else if refusal.detail.startsWith "A12Kernel.FlatRuleAssemblyError.errorFieldNotReferenced" then "unreferenced"
      else refusal.detail

private def conditions := [
  "FirstFilledValue(Rows/Body/N For Key, Fallback) > 0",
  "Sum(Rows/Body For Key) > 0",
  "MinValue(Rows/Body For Key) > 0",
  "MaxValue(Rows/Body For Key) > 0",
  "NumberOfDifferentValues(Rows/Body For Key) > 0"]

example : conditions.all (fun condition =>
    admission condition == "admitted" &&
    admission ("FieldFilled(Rows/Body/N) And " ++ condition) == "admitted") := by native_decide

example : conditions.all (fun condition =>
    admission ("FieldFilled(Rows/Other) And " ++ condition) == "iteration" &&
    admission condition "Rows/Code" == "unreferenced") := by native_decide


private def withPayload (prototype : FlatFieldDecl) : FlatModel := { model with
  fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 4 || field.id == 5 then
      { prototype with
        id := field.id, groupPath := field.groupPath, name := field.name,
        repeatableScope := field.repeatableScope }
    else field }

private def profiles : List FlatModel := [model,
  withPayload { id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .string } },
  withPayload { id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .boolean } },
  withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .enumeration },
    enumeration := some { storedTokens := ["A", "B"] } },
  withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .temporal .date .fullDate },
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
  withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .temporal .time .time },
    temporalTargetPolicy := some { format := "HH:mm:ss" } },
  withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .temporal .dateTime .now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
  withPayload {
    id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }]

private def selectedConditions := [
  "FirstFilledValue(Rows/Body/N For Key, Fallback) == [Fallback]",
  "FirstFilledValue(Rows/Body For Key, Fallback) == [Fallback]",
  "AtLeastOneFieldFilled(Rows/Body For Key)",
  "NumberOfFilledFields(Rows/Body For Key) > 0",
  "FieldFilled(Rows/Body/N For Key)",
  "GroupFilled(Rows/Body For Key)"]

example : profiles.all (fun profile => selectedConditions.all fun condition =>
    admission condition "Rows/Body/N" profile == "admitted" &&
    admission ("FieldFilled(Rows/Body/N) And " ++ condition) "Rows/Body/N" profile == "admitted") := by native_decide

example : profiles.all (fun profile => selectedConditions.all fun condition =>
    admission ("FieldFilled(Rows/Other) And " ++ condition) "Rows/Body/N" profile == "iteration" &&
    admission condition "Rows/Code" profile == "unreferenced") := by native_decide

example : profiles.all (fun profile => selectedConditions.all fun expression =>
    let condition := expression.replace "For Key" "For \"A\""
    admission condition "Rows/Body/N" profile == "admitted" &&
    admission ("FieldFilled(Rows/Other) And " ++ condition) "Rows/Body/N" profile == "iteration" &&
    admission ("FieldFilled(Rows/Body/N) And " ++ condition) "Rows/Body/N" profile == "admitted") := by native_decide

example : profiles.all (fun profile => selectedConditions.all fun condition =>
    admission condition "Key" profile == "admitted" &&
    admission (condition.replace "For Key" "For \"A\"") "Key" profile == "unreferenced") := by native_decide

example : admission "FirstFilledValue(Rows/Code For Key, Key) == \"A\"" "Rows/Code" = "admitted" ∧
    admission "FieldFilled(Rows/Other) And FirstFilledValue(Rows/Code For Key, Key) == \"A\"" "Rows/Code" = "iteration" ∧
    admission "FieldFilled(Rows/Code) And FirstFilledValue(Rows/Code For Key, Key) == \"A\"" "Rows/Code" = "admitted" := by native_decide


example : ["AtLeastOneGroupFilled(Key, Rows/Body For Key)",
    "NumberOfValueInFields(True In Rows/Body For Key) > 0",
    "NumberOfValueInFields(False In Rows/Body/N For Key, Fallback) > 0"].all (fun condition =>
    let profile := withPayload { id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .boolean } }
    admission condition "Rows/Body/N" profile == "admitted" &&
    admission ("FieldFilled(Rows/Other) And " ++ condition) "Rows/Body/N" profile == "iteration" &&
    admission ("FieldFilled(Rows/Body/N) And " ++ condition) "Rows/Body/N" profile == "admitted" &&
    admission condition "Rows/Code" profile == "unreferenced") := by native_decide

private def nestedProfile (profile : FlatModel) : FlatModel := { profile with
  fields := profile.fields.map (fun field => if field.id == 2 then field else
    { field with
      groupPath := ["Form", "Parents"] ++ field.groupPath.drop 1,
      repeatableScope := 20 :: field.repeatableScope }) ++ [
    { id := 7, groupPath := ["Form", "Parents"], name := "Other", repeatableScope := [20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 20, path := ["Form", "Parents"], repeatability := some 2 },
    { level := 10, path := ["Form", "Parents", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def nestedModel : FlatModel := nestedProfile model

example : nestedModel.validate.isOk = true ∧ conditions.all (fun expression =>
    let condition := (expression.replace "Rows/" "Parents/Rows/").replace "For Key" "For Parents/Key"
    admission ("FieldFilled(Parents/Other) And " ++ condition) "Parents/Rows/Body/N" nestedModel == "admitted" &&
    admission ("FieldFilled(Parents/Rows/Other) And " ++ condition) "Parents/Rows/Body/N" nestedModel == "iteration" &&
    admission ("FieldFilled(Parents/Rows/Body/N) And " ++ condition) "Parents/Rows/Body/N" nestedModel == "admitted") := by native_decide

example : conditions.all (fun expression =>
    let condition := "FieldFilled(Parents/Other) And " ++
      (expression.replace "Rows/" "Parents/Rows/").replace "For Key" "For Parents/Key"
    admission condition "Parents/Key" nestedModel == "admitted" &&
    admission (condition.replace "For Parents/Key" "For \"A\"") "Parents/Key" nestedModel == "unreferenced") := by native_decide

private def computationAdmits (condition : String) (fixture : FlatModel := model)
    (target : String := "../Rows/Out") : Bool :=
  (lowerComputation fixture .english {
    group := ["Form"], name := "Selected", targetRelPath := target,
    commonPrecondition := some condition, alternatives := [{ precondition := none, operation := "1" }],
    errorCodesToSuppress := [] }).isOk

example : profiles.all (fun profile => selectedConditions.all fun condition =>
    computationAdmits condition profile &&
    computationAdmits ("FieldFilled(Rows/Other) And " ++ condition) profile &&
    computationAdmits ("FieldFilled(Rows/Body/N) And " ++ condition) profile) := by native_decide

private def remainingCases : List (String × FlatModel) :=
  let strings := withPayload { id := 0, groupPath := ["Form"], name := "Payload", policy := { kind := .string } }
  [
    ("[Rows/Body/N For Key] PatternMatched \"[0-9]+\"", strings),
    ("Valid(Rows/Body/N For Key,\"Code\")", strings),
    ("[Rows/Body/N For Key] + \"x\" == [Fallback]", strings),
    ("AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Fallback)", model),
    ("AtLeastOneFieldValueIncludedInValueList(Fallback In Rows/Body For Key)", model),
    ("AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In Fallback)", strings),
    ("AtLeastOneFieldValueIncludedInValueList(Fallback In Rows/Body For Key)", strings),
    ("AtLeastOneFieldValueIncludedInValueList(Rows/Body For Key In \"A\")", strings)] ++
    (profiles.drop 4 |>.take 3).map fun profile => ("NumberOfDifferentValues(Rows/Body For Key) > 0", profile)

example : remainingCases.all (fun (condition, profile) =>
    admission condition "Rows/Body/N" profile == "admitted" &&
    admission ("FieldFilled(Rows/Other) And " ++ condition) "Rows/Body/N" profile == "iteration" &&
    admission ("FieldFilled(Rows/Body/N) And " ++ condition) "Rows/Body/N" profile == "admitted" &&
    admission condition "Rows/Code" profile == "unreferenced") := by native_decide

example : remainingCases.all (fun (expression, profile) =>
    let condition := expression.replace "For Key" "For \"A\""
    admission condition "Rows/Body/N" profile == "admitted" &&
    admission ("FieldFilled(Rows/Other) And " ++ condition) "Rows/Body/N" profile == "iteration" &&
    admission ("FieldFilled(Rows/Body/N) And " ++ condition) "Rows/Body/N" profile == "admitted" &&
    admission condition "Rows/Code" profile == "unreferenced") := by native_decide

example : remainingCases.all (fun (condition, profile) =>
    admission condition "Key" profile == "admitted" &&
    admission (condition.replace "For Key" "For \"A\"") "Key" profile == "unreferenced") := by native_decide

private def nestedCondition (condition : String) : String :=
  (condition.replace "Rows/" "Parents/Rows/").replace "For Key" "For Parents/Key"

example : remainingCases.all (fun (expression, profile) =>
    let fixture := nestedProfile profile
    fixture.validate.isOk && [expression, expression.replace "For Key" "For \"A\""].all fun expression =>
      let condition := "FieldFilled(Parents/Other) And " ++ nestedCondition expression
      admission condition "Parents/Rows/Body/N" fixture == "admitted" &&
      admission ("FieldFilled(Parents/Rows/Other) And " ++ condition) "Parents/Rows/Body/N" fixture == "iteration" &&
      admission ("FieldFilled(Parents/Rows/Body/N) And " ++ condition) "Parents/Rows/Body/N" fixture == "admitted" &&
      admission condition "Parents/Rows/Code" fixture == "unreferenced") := by native_decide

example : remainingCases.all (fun (expression, profile) =>
    let fixture := nestedProfile profile
    let condition := "FieldFilled(Parents/Other) And " ++ nestedCondition expression
    admission condition "Parents/Key" fixture == "admitted" &&
    admission (condition.replace "For Parents/Key" "For \"A\"") "Parents/Key" fixture == "unreferenced") := by native_decide

example : remainingCases.all (fun (condition, profile) =>
    [condition, condition.replace "For Key" "For \"A\""].all fun condition =>
      computationAdmits condition profile &&
      computationAdmits ("FieldFilled(Rows/Other) And " ++ condition) profile &&
      computationAdmits ("FieldFilled(Rows/Body/N) And " ++ condition) profile) := by native_decide

example : remainingCases.all (fun (expression, profile) =>
    let fixture := nestedProfile profile
    [expression, expression.replace "For Key" "For \"A\""].all fun expression =>
      let condition := "FieldFilled(Parents/Other) And " ++ nestedCondition expression
      computationAdmits condition fixture "../Parents/Rows/Out" &&
      computationAdmits ("FieldFilled(Parents/Rows/Other) And " ++ condition) fixture "../Parents/Rows/Out" &&
      computationAdmits ("FieldFilled(Parents/Rows/Body/N) And " ++ condition) fixture "../Parents/Rows/Out") := by native_decide

end A12Kernel.Dm.SelectedReferenceAdmissionLocks
