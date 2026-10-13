import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.ValidationCondition.Omission

namespace A12Kernel.Dm.MessageReferenceLocks

private def model : FlatModel :=
  let field (id : Nat) (name : String) (groupPath : GroupPath) (repeatableScope : List Nat) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope, policy := { kind := .number { scale := 0, signed := true } } }
  { fields := [field 1 "Anchor" ["Form", "Rows"] [10],
      field 2 "N" ["Form", "Rows", "A"] [10],
      field 3 "N" ["Form", "Rows", "Items"] [10, 20],
      field 4 "M" ["Form", "Rows", "Items", "Fixed"] [10, 20],
      field 5 "V" ["Form", "Rows", "Items", "Deep"] [10, 20, 30]]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 },
      { level := 30, path := ["Form", "Rows", "Items", "Deep"], repeatability := some 2 }] }

private def rule? (operand : String) : Option (CheckedResolvedValidationRule model) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  (checkRule dm .english {
    name := "Reference", group := ["Form", "Rows"], errorCode := "REF", errorEntityRelPath := "../Anchor",
    severity := "ERROR", condition := "FieldFilled(Anchor) And NumberOfFilledGroups(A," ++ operand ++ ") > 0" }).toOption

private def references? (operand : String) (row : Nat) : Option (List MessagePointer) := do
  let rule ← rule? operand
  (rule.condition.core.referencePointers [(10, row)]).toOption

example : (rule? "Items*").isSome && (rule? "Items*/Fixed").isSome = true := by native_decide

example : references? "Items*" 2 = some [
    { field := 1, coordinates := [.concrete 2] },
    { field := 2, coordinates := [.concrete 2] },
    { field := 3, coordinates := [.concrete 2, .wildcard] },
    { field := 4, coordinates := [.concrete 2, .wildcard] },
    { field := 5, coordinates := [.concrete 2, .wildcard, .wildcard] }] := by native_decide

example : references? "Items*/Fixed" 1 = some [
    { field := 1, coordinates := [.concrete 1] },
    { field := 2, coordinates := [.concrete 1] },
    { field := 4, coordinates := [.concrete 1, .wildcard] }] := by native_decide

private def omissionModel : FlatModel :=
  let number (id : Nat) (name : String) (groupPath : GroupPath := ["Form"])
      (repeatableScope : List Nat := []) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope, policy := { kind := .number { scale := 0, signed := true } } }
  { fields := [number 1 "Missing", number 2 "P", number 3 "Q", number 4 "Limit",
      number 5 "N" ["Form", "Addr"], number 6 "M" ["Form", "Addr"],
      number 7 "Qty" ["Form", "Lines"] [40], number 8 "Picked" ["Form", "Lines"] [40],
      { id := 9, name := "Span", groupPath := ["Form", "Lines"], repeatableScope := [40],
        policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 10, name := "Range", groupPath := ["Form"],
        policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
      { id := 11, name := "Due", groupPath := ["Form"],
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } }]
    repeatableGroups := [{ level := 40, path := ["Form", "Lines"], repeatability := some 2 }] }

private def omissionRule? (condition : String) : Option (CheckedResolvedValidationRule omissionModel) :=
  (checkRule { flat := omissionModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Omission", group := ["Form"], errorCode := "OMIT", errorEntityRelPath := "../Missing",
      severity := "ERROR", condition := condition ++ " And FieldNotFilled(Missing)" }).toOption

private def sets? (condition : String) : Option (List String × List String) := do
  let rule ← omissionRule? condition
  let all ← (rule.condition.core.referencePointers []).toOption
  let omission ← (rule.condition.core.omissionPointers []).toOption
  pure ((all.map (renderPointer omissionModel)).mergeSort,
    (omission.map (renderPointer omissionModel)).mergeSort)

private def cases : List (String × List String × List String) := [
  ("DateRangesOverlap(Lines*/Span Having [Lines/Picked] > 0)",
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Span", "Form/Missing"],
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Span", "Form/Missing"]),
  ("AtLeastOneDateRangeOverlaps(Range In Lines*/Span Having [Lines/Picked] > 0)",
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Span", "Form/Missing", "Form/Range"],
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Span", "Form/Missing", "Form/Range"]),
  ("DayFromDate(AddDays(Due,NumberOfFilledFields(P,Q))) > 0",
    ["Form/Due", "Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("0 < DayFromDate(AddDays(Due,NumberOfDifferentValues(P,Q)))",
    ["Form/Due", "Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("AddDays(Due,NumberOfFilledFields(P,Q)) > [Due]",
    ["Form/Due", "Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("[Due] < AddDays(Due,NumberOfDifferentValues(P,Q))",
    ["Form/Due", "Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("DayFromDate(AddDays(Due,NumberOfFilledFields(P,Q))) < 2",
    ["Form/Due", "Form/Missing", "Form/P", "Form/Q"], ["Form/Due", "Form/Missing", "Form/P", "Form/Q"]),
  ("DayFromDate(AddDays(Due,NumberOfFilledFields(P,Q))) > NumberOfFilledFields(Missing,Limit)",
    ["Form/Due", "Form/Limit", "Form/Missing", "Form/P", "Form/Q"],
    ["Form/Due", "Form/Limit", "Form/Missing", "Form/P", "Form/Q"]),
  ("FieldFilled(P)", ["Form/Missing", "Form/P"], ["Form/Missing"]),
  ("AtLeastOneFieldFilled(P,Q)", ["Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("MoreThanOneFieldFilled(P,Q)", ["Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("NoFieldFilled(P,Q)", ["Form/Missing", "Form/P", "Form/Q"], ["Form/Missing", "Form/P", "Form/Q"]),
  ("NumberOfFilledFields(P,Q) > [Limit]", ["Form/Limit", "Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("[Limit] <= NumberOfFilledFields(P,Q)", ["Form/Limit", "Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("NumberOfFilledFields(P,Q) < 2", ["Form/Missing", "Form/P", "Form/Q"], ["Form/Missing", "Form/P", "Form/Q"]),
  ("NumberOfFilledFields(P,Q) == 0", ["Form/Missing", "Form/P", "Form/Q"], ["Form/Missing", "Form/P", "Form/Q"]),
  ("NumberOfDifferentValues(P,Q) > 0", ["Form/Missing", "Form/P", "Form/Q"], ["Form/Missing"]),
  ("NumberOfFilledFields(P,Q) > NumberOfFilledFields(Missing,Limit)", ["Form/Limit", "Form/Missing", "Form/P", "Form/Q"], ["Form/Limit", "Form/Missing", "Form/P", "Form/Q"]),
  ("GroupFilled(Addr)", ["Form/Addr/M", "Form/Addr/N", "Form/Missing"], ["Form/Missing"]),
  ("GroupNotFilled(Addr)", ["Form/Addr/M", "Form/Addr/N", "Form/Missing"], ["Form/Addr/M", "Form/Addr/N", "Form/Missing"]),
  ("GroupFilled(/Form)", ["Form/Missing"], ["Form/Missing"]),
  ("AtLeastOneGroupFilled(/Form)", ["Form/Missing"], ["Form/Missing"]),
  ("AllFieldsFilled(Lines*/Qty Having [Lines/Picked] > 0)",
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Qty", "Form/Missing"],
    ["/Form[1]/Lines[0]/Picked", "Form/Missing"]),
  ("NumberOfFilledFields(Lines*/Qty Having [Lines/Picked] > 0) > [Limit]",
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Qty", "Form/Limit", "Form/Missing"],
    ["/Form[1]/Lines[0]/Picked", "Form/Missing"])]

example : sets? "FieldFilled(P)" = some (["Form/Missing", "Form/P"], ["Form/Missing"]) := by native_decide

example : cases.all (fun (condition, _, _) => (omissionRule? condition).isSome) = true := by native_decide
example : cases.all (fun (condition, all, omission) => sets? condition == some (all, omission)) = true := by native_decide

private def capturedMessage? : Option (List (String × String × List String × List String)) := do
  let dm : DmModel := { flat := omissionModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let rule ← (checkRule dm .english {
    name := "Captured", group := ["Form"], errorCode := "CAPTURED", errorEntityRelPath := "../Lines/Qty", severity := "ERROR",
    condition := "AllFieldsFilled(Lines*/Qty Having [Lines/Picked] > [$Lines/Picked]) And FieldNotFilled(Lines/Qty)" }).toOption
  let world : World := { now := { epochMillis := 0 } }
  let row (qty picked : String) := Lean.Json.mkObj [("Qty", .str qty), ("Picked", .str picked)]
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Lines", .arr #[row "1" "2", row "" "0"])])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler omissionModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  let outputs ← outcomes.mapM fun (environment, outcome) => do
    match outcome.message? with
    | none => pure []
    | some message =>
        let references ← (rule.condition.core.messageReferences message environment).toOption
        let observed := observe omissionModel message
        pure [(observed.pointer, observed.messageType,
          (references.referenced.map (renderPointer omissionModel)).mergeSort,
          (references.fillToFix.map (renderPointer omissionModel)).mergeSort)]
  pure outputs.flatten

example : capturedMessage? = some [("Form/Lines[2]/Qty", "OMISSION_ERROR",
    ["/Form[1]/Lines[0]/Picked", "/Form[1]/Lines[0]/Qty", "Form/Lines[2]/Picked", "Form/Lines[2]/Qty"],
    ["/Form[1]/Lines[0]/Picked", "Form/Lines[2]/Picked", "Form/Lines[2]/Qty"])] := by native_decide

example : ((omissionRule? "[P] > 0").bind fun rule =>
    (rule.core.emit (.fired .value)).message?.bind fun message =>
      (rule.condition.core.messageReferences message []).toOption.map (·.fillToFix)) = some [] := by native_decide

private def subtreeModel : FlatModel :=
  let field (id : Nat) (name : String) (groupPath : GroupPath) (repeatableScope : List Nat) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope, policy := { kind := .number { scale := 0, signed := true } } }
  { fields := [field 1 "Anchor" ["Form"] [],
      field 2 "N" ["Form", "Other"] [],
      field 3 "M" ["Form", "Parent", "Children"] [10],
      field 4 "N" ["Form", "Parent", "Children"] [10],
      field 5 "K" ["Form", "Parent", "Children", "Parts"] [10, 20]]
    repeatableGroups := [
      { level := 10, path := ["Form", "Parent", "Children"], repeatability := some 2 },
      { level := 20, path := ["Form", "Parent", "Children", "Parts"], repeatability := some 2 }] }

/-- A fixed group count over a group holding repeatable levels the rule does not bind references every
row of them: the unbound level and each deeper one are wildcarded rather than refused. Kernel oracle:
the retained group-relevance-union capture's `CountZero` messages. -/
example : (do
    let dm : DmModel := { flat := subtreeModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    let rule ← (checkRule dm .english {
      name := "CountZero", group := ["Form"], errorCode := "CountZero", errorEntityRelPath := "../Anchor",
      severity := "ERROR", condition := "FieldFilled(Anchor) And NumberOfFilledGroups(Parent, Other) == 0" }).toOption
    let pointers ← (rule.condition.core.referencePointers []).toOption
    pure ((pointers.map (renderPointer subtreeModel)).mergeSort (compare · · != .gt))) =
    some ["/Form[1]/Parent[1]/Children[0]/M", "/Form[1]/Parent[1]/Children[0]/N",
      "/Form[1]/Parent[1]/Children[0]/Parts[0]/K", "Form/Anchor", "Form/Other/N"] := by
  native_decide

end A12Kernel.Dm.MessageReferenceLocks
