import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.HavingComparisonLocks
open Lean A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "Error", policy := { kind := .string } },
    { id := 2, groupPath := ["Form"], name := "Expected", policy := { kind := .string } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Tag", policy := { kind := .string }, repeatableScope := [10] },
    { id := 4, groupPath := ["Form", "Rows"], name := "N", policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] },
    { id := 5, groupPath := ["Form"], name := "Out", policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def runModel (model : FlatModel) (filter : String) (fresh : Bool)
    (expected first second : String) (producerOperation : String := "\"drop\"") : Option (Verdict × List String) := do
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := fun (tag n : String) => Json.mkObj [("Tag", Json.str tag), ("N", Json.str n)]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Error", Json.str "ready"), ("Expected", Json.str expected),
    ("Rows", Json.arr #[row first "2", row second "5", row first "7"])])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(Rows*/N Having " ++ filter ++ ")"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And " ++ operation ++ " == 9", severity := "ERROR" }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let (_, computation) ← (lowerComputation model .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let computations ← if fresh then do
      let (_, producer) ← (lowerComputation model .english {
        group := ["Form"], name := "Expected", targetRelPath := "../Expected", commonPrecondition := none,
        alternatives := [{ precondition := none, operation := producerOperation }], errorCodesToSuppress := [] }).toOption
      pure [computation, producer]
    else pure [computation]
  let outcomes ← (runComputations world prepared document computations).toOption
  pure (verdict, outcomes.map (·.outcome))

private def run (filter : String) (fresh : Bool := false)
    (kind : FieldKind := .string) (expected : String := "keep")
    (first : String := "keep") (second : String := "drop")
    (enumeration : Option EnumerationDeclaration := none) : Option (Verdict × List String) :=
  runModel { model with fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then { field with policy := { kind }, enumeration } else field }
    filter fresh expected first second

example : run "[Rows/Tag] == [$Expected]" = some (.fired .omission, ["value 9"]) ∧
    run "[$Expected] == [Rows/Tag]" = some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] != [$Expected]" = some (.notFired, ["value 5"]) := by native_decide

example : (run "[Rows/Tag] == [$Expected]" true).map (·.2) = some ["value drop", "value 5"] := by native_decide

example : run "[Rows/Tag] == [$Expected]" false .boolean "false" "false" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] == False" false .boolean "true" "false" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "True != [Rows/Tag]" false .confirm "true" "" "true" =
      some (.fired .omission, ["value 9"]) := by native_decide

private def domain : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Swap", tokens := ["drop", "keep"] }] }

example : run "[Rows/Tag] == [$Expected]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag -> Swap] == [$Expected]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.notFired, ["value 5"]) ∧
    run "[Rows/Tag -> Swap] == [$Expected -> Swap]" false .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) := by native_decide


example : run "[Rows/Tag] == False" false .confirm "true" "true" "" = none ∧
    run "[Rows/Tag] == [$Expected]" false .confirm "true" "true" "" = none ∧
    run "[Rows/Tag] != [$Expected]" false .confirm "true" "" "true" =
      some (.fired .omission, ["value 9"]) ∧
    run "[Rows/Tag] == False" false .boolean "false" "bad" "false" =
      some (.notFired, []) := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, \"keep\", \"extra\")" =
      some (.fired .omission, ["value 9"]) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, \"keep\")" =
      some (.notFired, ["value 5"]) ∧
    run "FieldValueIncludedInValueList(Rows/Tag, 2, 7)" false
      (.number { scale := 0, signed := true }) "2" "2" "5" =
      some (.fired .omission, ["value 9"]) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, 2)" false
      (.number { scale := 0, signed := true }) "2" "2" "5" =
      some (.notFired, ["value 5"]) := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, \"keep\")" false
      .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, \"keep\")" false
      .enumeration "keep" "keep" "drop" (some domain) =
      some (.notFired, ["value 5"]) := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag -> Swap, \"drop\")" false
      .enumeration "keep" "keep" "drop" (some domain) =
      some (.fired .omission, ["value 9"]) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag -> Swap, \"drop\")" false
      .enumeration "keep" "keep" "drop" (some domain) =
      some (.notFired, ["value 5"]) := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, 0)" false
      (.number { scale := 0, signed := true }) "0" "" "0" =
      some (.notFired, ["value 5"]) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, 0)" false
      (.number { scale := 0, signed := true }) "0" "" "0" =
      some (.notFired, ["value 0"]) ∧
    run "FieldValueIncludedInValueList(Rows/Tag, -2)" false
      (.number { scale := 0, signed := true }) "0" "-2" "5" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, \"\", \"keep\")" false .string "keep" "" "keep" =
      some (.notFired, ["value 5"]) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, \"keep\")" false .string "keep" "" "keep" =
      some (.notFired, ["value 0"]) ∧
    run "FieldValueIncludedInValueList(Rows/Tag, 2)" false
      (.number { scale := 0, signed := true }) "0" "bad" "2" =
      some (.notFired, []) ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, 2)" false
      (.number { scale := 0, signed := true }) "0" "bad" "5" =
      some (.notFired, []) := by native_decide

example : (run "FieldFilled(Rows/Tag) And FieldValueIncludedInValueList($Expected, \"keep\")" true).map (·.2) =
      some ["value drop", "value 0"] ∧
    (run "FieldFilled(Rows/Tag) And FieldValueNotIncludedInValueList($Expected, \"keep\")" true).map (·.2) =
      some ["value drop", "value 14"] := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, \"absent\")" false .enumeration
      "keep" "keep" "drop" (some domain) = none ∧
    run "FieldValueIncludedInValueList(Rows/Tag -> Missing, \"keep\")" false .enumeration
      "keep" "keep" "drop" (some domain) = none ∧
    run "FieldValueIncludedInValueList(Rows/Tag, 2.5)" false
      (.number { scale := 1, signed := true }) "2" "2" "5" = none ∧
    run "FieldValueIncludedInValueList(Rows/Tag, \"true\")" false .boolean "true" "true" "false" = none := by native_decide

example : run "FieldValueIncludedInValueList($Expected, \"keep\") And [Rows/Tag] == \"keep\"" true =
      some (.fired .omission, ["value drop", "value 0"]) ∧
    run "FieldValueNotIncludedInValueList($Expected, \"drop\") And [Rows/Tag] == \"keep\"" true =
      some (.fired .omission, ["value drop", "value 0"]) := by native_decide

private def fieldMembershipFilters : List String := [
  "FieldValueIncludedInValueList(Rows/Tag, [$Expected])",
  "FieldValueNotIncludedInValueList(Rows/Tag, [$Expected])",
  "AtLeastOneFieldValueIncludedInValueList(Rows/Tag In $Expected)",
  "NoFieldValueIncludedInValueList(Rows/Tag In $Expected)",
  "NotAllFieldValuesIncludedInValueList(Rows/Tag In $Expected)"]

private def membershipResults : List (Option (Verdict × List String)) := [
  some (.fired .omission, ["value 9"]), some (.notFired, ["value 5"]),
  some (.fired .omission, ["value 9"]), some (.notFired, ["value 5"]),
  some (.notFired, ["value 5"])]

example : fieldMembershipFilters.map (fun filter => run filter) = membershipResults ∧
    fieldMembershipFilters.map (fun filter => run filter false
      (.number { scale := 0, signed := true }) "2" "2" "5") = membershipResults ∧
    fieldMembershipFilters.map (fun filter => run filter false
      .enumeration "keep" "keep" "drop" (some domain)) = membershipResults := by native_decide

private def membershipDiagnostic (model : FlatModel) (filter : String) : Option (Option KernelStaticDiagnostic) := do
  let parsed ← (parseText .english filter).toOption
  let authored ← (lowerHaving parsed.body).toOption
  let source ← (elaborateStarFieldPath model ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  pure (match elaborateStarHavingCore model ["Form"] source authored with
    | .ok _ => none
    | .error error => error.diagnostic?)

private def categoryModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .enumeration }, enumeration := some domain }
  else field }

example : [
    "FieldValueIncludedInValueList(Rows/Tag, [$Expected -> Missing])",
    "FieldValueNotIncludedInValueList(Rows/Tag -> Missing, [$Expected])",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Tag -> Missing In $Expected)",
    "NoFieldValueIncludedInValueList(Rows/Tag -> Missing, Rows/N In $Expected)",
    "NotAllFieldValuesIncludedInValueList(Rows/Tag In $Expected -> Missing, $Expected -> Missing)"
  ].map (membershipDiagnostic categoryModel) = List.replicate 5 (some (some .categoryUnknown)) ∧
    membershipDiagnostic categoryModel
      "AtLeastOneFieldValueIncludedInValueList(Rows/Tag -> Swap In $Expected)" = some none := by native_decide

private def temporalMembershipModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then
    { field with policy := {
        kind := .temporal (if field.id == 2 then .time else .date)
          (TemporalComponents.ofFormat (if field.id == 2 then "HH:mm:ss" else "yyyy-MM-dd")) } }
  else field }

example : [
    "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, $Expected In Rows/N)",
    "NoFieldValueIncludedInValueList($Expected, Rows/Tag In Rows/N)",
    "NotAllFieldValuesIncludedInValueList(Rows/Tag In Rows/N)"
  ].map (membershipDiagnostic temporalMembershipModel) =
    List.replicate 3 (some (some .onlyStringEnumNumberAllowed)) ∧
    membershipDiagnostic temporalMembershipModel
      "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, Rows/N In $Expected)" =
      some (some .varyingTypesNotAllowed) := by native_decide

private def literalListFilters : List String := [
  "AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList", "NotAllFieldValuesIncludedInValueList"]

example : literalListFilters.map (fun operator => run (operator ++ "(Rows/Tag In \"keep\")")) =
    [some (.fired .omission, ["value 9"]), some (.notFired, ["value 5"]), some (.notFired, ["value 5"])] ∧
    literalListFilters.map (fun operator => run (operator ++ "(Rows/Tag In \"keep\")")
      false .enumeration "keep" "keep" "drop" (some domain)) =
    [some (.fired .omission, ["value 9"]), some (.notFired, ["value 5"]), some (.notFired, ["value 5"])] := by native_decide

example : literalListFilters.map (fun operator => (run (operator ++ "(Rows/Tag -> Swap In \"keep\")")
      false .enumeration "keep" "keep" "drop" (some domain)).map (·.2)) =
    [some ["value 5"], some ["value 9"], some ["value 9"]] ∧
    literalListFilters.map (fun operator => (run (operator ++ "(Rows/Tag, $Expected In \"keep\")") true).map (·.2)) =
    [some ["value drop", "value 9"], some ["value drop", "value 5"], some ["value drop", "value 14"]] := by native_decide

example : literalListFilters.map (fun operator => (run (operator ++ "(Rows/Tag In \"\", \"keep\")")
      false .string "keep" "" "keep").map (·.2)) =
    [some ["value 5"], some ["value 9"], some ["value 0"]] ∧
    run "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, Rows/Tag In \"keep\")" = none ∧
    run "AtLeastOneFieldValueIncludedInValueList([Rows/Tag] In \"keep\")" = none := by native_decide

private def disjointLiteralDomains : FlatModel := { categoryModel with fields := categoryModel.fields.map fun field =>
  if field.id == 2 then { field with enumeration := some { storedTokens := ["other", "extra"] } } else field }

example : literalListFilters.map (fun operator =>
    (runModel disjointLiteralDomains (operator ++ "(Rows/Tag, $Expected In \"keep\", \"other\")")
      false "other" "keep" "drop").map (·.2)) =
    [some ["value 14"], some ["value 0"], some ["value 5"]] ∧
    literalListFilters.map (fun operator => (run
      (operator ++ "(Rows/Tag, Rows/Tag -> Swap In \"keep\", \"drop\")")
      false .enumeration "keep" "keep" "drop" (some domain)).map (·.2)) =
    [some ["value 14"], some ["value 0"], some ["value 0"]] := by native_decide

example : membershipDiagnostic disjointLiteralDomains
    "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, $Expected In \"absent\")" =
      some (some .invalidStringConstantForEnumComparison) ∧
    membershipDiagnostic categoryModel "NoFieldValueIncludedInValueList(Rows/Tag -> Missing, Rows/N In \"keep\")" =
      some (some .categoryUnknown) ∧
    membershipDiagnostic model "NotAllFieldValuesIncludedInValueList(Rows/N In \"1\")" =
      some (some .invalidTypesForComparison) ∧
    membershipDiagnostic model "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, Rows/N In \"keep\")" =
      some (some .varyingTypesNotAllowed) := by native_decide

private def categoryLiteralDomains : FlatModel := { categoryModel with fields := categoryModel.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with enumeration := some {
    storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["yes", "no"] }] } }
  else field }

private def categoryLiteralCertificate (value : String) : Option Bool := do
  let declaration ← (categoryLiteralDomains.lookupUniqueId 3).toOption
  let (operand, _) ← declaration.toEnumerationTextFieldComparison? (.category "Label")
  pure ((HavingFieldValueList.tokenLiterals [{ origin := .inner, operand }] [value]).wellFormedForEnvironments
    (.quantified .atLeastOne) categoryLiteralDomains [10] [])

example : literalListFilters.map (fun operator =>
    (runModel categoryLiteralDomains (operator ++ "(Rows/Tag -> Label In \"yes\")")
      false "keep" "keep" "drop").map (·.2)) =
    [some ["value 9"], some ["value 5"], some ["value 5"]] ∧
    literalListFilters.map (fun operator => membershipDiagnostic categoryLiteralDomains
      (operator ++ "(Rows/Tag -> Label In \"keep\")")) =
      List.replicate 3 (some (some .invalidStringConstantForEnumComparison)) ∧
    literalListFilters.map (fun operator =>
      (runModel categoryLiteralDomains (operator ++ "(Rows/Tag, Rows/Tag -> Label In \"keep\", \"yes\")")
        false "keep" "keep" "drop").map (·.2)) =
      [some ["value 9"], some ["value 5"], some ["value 5"]] ∧
    categoryLiteralCertificate "yes" = some true ∧ categoryLiteralCertificate "keep" = some false := by native_decide

private def offPathLiteralModel : FlatModel := { model with
  fields := model.fields ++ [{
    id := 6, groupPath := ["Form", "Other"], name := "Text", repeatableScope := [20], policy := { kind := .string } }]
  repeatableGroups := model.repeatableGroups ++ [{ level := 20, path := ["Form", "Other"], repeatability := some 3 }] }

example : membershipDiagnostic offPathLiteralModel
    "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, Other/Text In \"keep\")" =
      some (some .invalidIterationInFilterCondition) ∧
    membershipDiagnostic offPathLiteralModel
    "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, Other/Text In \"keep\") And [Rows/N] == \"bad\"" =
      some (some .invalidCompareToEnumOrString) := by native_decide

private def reversedMembershipResults : List (Option (Verdict × List String)) := [
  some (.notFired, ["value 5"]), some (.fired .omission, ["value 9"]),
  some (.notFired, ["value 5"]), some (.fired .omission, ["value 9"]),
  some (.fired .omission, ["value 9"])]

example : fieldMembershipFilters.map (fun filter => run (filter.replace "Rows/Tag" "Rows/Tag -> Swap")
      false .enumeration "keep" "keep" "drop" (some domain)) = reversedMembershipResults ∧
    fieldMembershipFilters.map (fun filter => run (filter.replace "$Expected" "$Expected -> Swap")
      false .enumeration "keep" "keep" "drop" (some domain)) = reversedMembershipResults ∧
    fieldMembershipFilters.map (fun filter => run ((filter.replace "Rows/Tag" "Rows/Tag -> Swap").replace "$Expected" "$Expected -> Swap")
      false .enumeration "keep" "keep" "drop" (some domain)) = membershipResults := by native_decide

example : fieldMembershipFilters.map (fun filter => (run filter true).map (·.2)) =
    [some ["value drop", "value 5"], some ["value drop", "value 9"],
     some ["value drop", "value 5"], some ["value drop", "value 9"],
     some ["value drop", "value 9"]] := by native_decide

private def emptySubjectResults : List (Option (Verdict × List String)) := [
  some (.notFired, ["value 5"]), some (.notFired, ["value 0"]),
  some (.notFired, ["value 5"]), some (.fired .omission, ["value 9"]),
  some (.notFired, ["value 0"])]

example : fieldMembershipFilters.map (fun filter => run filter false .string "keep" "" "keep") = emptySubjectResults ∧
    fieldMembershipFilters.map (fun filter => run filter false
      (.number { scale := 0, signed := true }) "0" "" "0") = emptySubjectResults ∧
    fieldMembershipFilters.map (fun filter => (run filter false
      (.number { scale := 0, signed := true }) "2" "bad" "2").map (·.2)) =
      [some [], some [], some [], some [], some []] := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, [Rows/Tag])" = none ∧
    run "AtLeastOneFieldValueIncludedInValueList(Rows/Tag, Rows/Tag In $Expected)" = none ∧
    run "NoFieldValueIncludedInValueList(Rows/Tag In $Expected, $Expected)" = none := by native_decide

private def differentEnumerationDomains : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .enumeration }, enumeration := some {
      storedTokens := if field.id == 2 then ["keep", "other"] else ["keep", "drop"] } }
  else field }

example : fieldMembershipFilters.map (fun filter =>
    runModel differentEnumerationDomains filter false "keep" "keep" "drop") = membershipResults := by native_decide

example : ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList",
      "NotAllFieldValuesIncludedInValueList"].map (fun operator =>
      (run (operator ++ "(Rows/Tag, Rows/N In $Expected)") false
        (.number { scale := 0, signed := true }) "2" "2" "5").map (·.2)) =
    [some ["value 9"], some ["value 5"], some ["value 12"]] ∧
    (run "FieldValueIncludedInValueList(Rows/Tag, [$Expected], [Rows/N])" false
      (.number { scale := 0, signed := true }) "2" "2" "5").map (·.2) = some ["value 14"] ∧
    run "FieldValueIncludedInValueList(Rows/Tag, [Rows/N], [$Expected])" false
      (.number { scale := 0, signed := true }) "bad" "2" "5" = some (.notFired, []) := by native_decide

example : (run "AtLeastOneFieldValueIncludedInValueList(Rows/Tag In Rows/Tag -> Swap)" false
      .enumeration "keep" "keep" "drop" (some domain)).map (·.2) = some ["value 0"] ∧
    (run "NotAllFieldValuesIncludedInValueList(Rows/Tag In Rows/Tag -> Swap)" false
      .enumeration "keep" "keep" "drop" (some domain)).map (·.2) = some ["value 14"] := by native_decide

example : run "FieldValueIncludedInValueList(Rows/Tag, $Expected)" = none ∧
    run "FieldValueNotIncludedInValueList(Rows/Tag, $Expected)" = none ∧
    run "AtLeastOneFieldValueIncludedInValueList([Rows/Tag] In $Expected)" = none ∧
    run "NotAllFieldValuesIncludedInValueList(Rows/Tag In [$Expected])" = none := by native_decide

private def referencesFor (filter : String) (modelOverride : FlatModel := model) (carrier : String := "Tag") : Option (Bool × Bool) := do
  let parsed ← (parseText .english
    ("FieldValuesNotUnique(/Form/Rows*/" ++ carrier ++ " Having " ++ filter ++ ")")).toOption
  let checked ← (lowerCondition modelOverride ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (pointers.contains { field := 3, coordinates := [.wildcard] },
    pointers.contains { field := 3, coordinates := [.concrete 2] })

example : referencesFor "[/Form/Rows/Tag] == [$/Form/Rows/Tag]" = some (true, true) := by native_decide

example : referencesFor
    "FieldValueIncludedInValueList(/Form/Rows/Tag, \"keep\") And FieldValueNotIncludedInValueList($/Form/Rows/Tag, \"drop\")" =
      some (true, true) := by native_decide

example : referencesFor "FieldValueIncludedInValueList(/Form/Rows/Tag, [$/Form/Rows/Tag])" =
      some (true, true) ∧
    referencesFor "NotAllFieldValuesIncludedInValueList(/Form/Rows/Tag In $/Form/Rows/Tag)" =
      some (true, true) := by native_decide

example : referencesFor
    "NotAllFieldValuesIncludedInValueList(/Form/Rows/Tag, $/Form/Rows/Tag In \"keep\")" =
      some (true, true) := by native_decide

private def toleranceRanges : List Nat := [1, 2, 5, 10]

example : toleranceRanges.map (fun band =>
    (run s!"[Rows/Tag] * {band} DiffersWithToleranceRange{band} [$Expected] * {band}"
      false (.number { scale := 0, signed := true }) "3" "2" "5").map (·.2)) =
    List.replicate 4 (some ["value 5"]) ∧
    toleranceRanges.map (fun band =>
      (run s!"3 * {band} DiffersWithToleranceRange{band} [Rows/N] * {band}").map (·.2)) =
    List.replicate 4 (some ["value 12"]) := by native_decide

example : run "[Rows/Tag] DiffersWithToleranceRange1 0" false
      (.number { scale := 1, signed := true }) "0" "1.0" "1.1" =
      some (.notFired, ["value 5"]) ∧
    run "[Rows/Tag] DiffersWithToleranceRange1 1" false
      (.number { scale := 0, signed := true }) "0" "" "3" =
      some (.notFired, ["value 5"]) ∧
    run "[Rows/Tag] DiffersWithToleranceRange1 1" false
      (.number { scale := 0, signed := true }) "0" "bad" "3" =
      some (.notFired, []) := by native_decide

example : run "[Rows/N] DiffersWithToleranceRange3 0" = none ∧
    run "1 DiffersWithToleranceRange1 0" = none ∧
    run "[Rows/Tag] DiffersWithToleranceRange1 0" = none := by native_decide

example : toleranceRanges.map (fun band =>
    (run s!"CurrentRepetition(Rows) * {band} DiffersWithToleranceRange{band} {band}").map (·.2)) =
      List.replicate 4 (some ["value 7"]) := by native_decide

private def toleranceModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .number { scale := if field.id == 2 then 0 else 1, signed := true } } }
  else field }

example : runModel toleranceModel "[Rows/Tag] DiffersWithToleranceRange1 [$Expected]"
      false "3" "2.0" "5.0" = some (.notFired, ["value 5"]) ∧
    runModel toleranceModel "[$Expected] DiffersWithToleranceRange1 [Rows/Tag]"
      false "3" "2.0" "5.0" = some (.notFired, ["value 5"]) ∧
    runModel toleranceModel "[Rows/Tag] == [$Expected]" false "3" "2.0" "5.0" = none ∧
    runModel toleranceModel "[Rows/Tag] DiffersWithToleranceRange1 [$Expected]"
      true "3" "2.0" "5.0" "0" = some (.notFired, ["value 0", "value 14"]) := by native_decide

private def toleranceReferences : Option (Bool × Bool) := do
  let parsed ← (parseText .english
    "FieldValuesNotUnique(/Form/Rows*/Tag Having [/Form/Rows/N] DiffersWithToleranceRange1 [$/Form/Rows/N])").toOption
  let checked ← (lowerCondition model ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (pointers.contains { field := 4, coordinates := [.wildcard] },
    pointers.contains { field := 4, coordinates := [.concrete 2] })

example : toleranceReferences = some (true, true) := by native_decide

private def temporalRun (filter : String) (leftKind rightKind : TemporalKind)
    (leftFormat rightFormat expected first second : String)
    (partialMode : TemporalPartialMode := .full) (baseYear : Option Int := none) : Option (Verdict × List String) :=
  let fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      let kind := if field.id == 3 then leftKind else rightKind
      let format := if field.id == 3 then leftFormat else rightFormat
      { field with
        policy := { kind := .temporal kind (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format, partialMode } }
    else field
  runModel { model with fields, baseYear } filter false expected first second

private def dateRun (filter : String) (first : String := "2024-01-01") := temporalRun filter .date .date
  "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" first "2024-01-03"

example : ["==", "!=", "<", "<=", ">", ">="].map (fun op =>
    (dateRun ("[Rows/Tag] " ++ op ++ " [$Expected]")).map (·.2)) =
      [some ["value 0"], some ["value 14"], some ["value 9"], some ["value 9"],
       some ["value 5"], some ["value 5"]] ∧
    (dateRun "[$Expected] < [Rows/Tag]").map (·.2) = some ["value 5"] ∧
    (dateRun "[Rows/Tag] < [$Expected]").map (·.1) = some (.fired .omission) := by native_decide

example : ["==", "!=", "<", "<=", ">", ">="].map (fun op =>
    dateRun ("[Rows/Tag] " ++ op ++ " [$Expected]") "2024-01-02") =
      [some (.fired .omission, ["value 9"]), some (.notFired, ["value 5"]),
       some (.notFired, ["value 0"]), some (.fired .omission, ["value 9"]),
       some (.notFired, ["value 5"]), some (.notFired, ["value 14"])] := by native_decide

example : [TemporalKind.date, .dateTime, .time].all (fun kind =>
    temporalRun "[Rows/Tag] == [$Expected]" kind kind "HH:mm:ss" "HH:mm:ss"
      "12:30:00" "12:30:00" "15:30:00" == some (.fired .omission, ["value 9"])) = true := by native_decide

example : temporalRun "[Rows/Tag] < [$Expected]" .date .dateTime
    "yyyy-MM-dd" "yyyy-MM-dd'T'HH:mm:ss" "2024-01-02T12:00:00" "2024-01-01" "2024-01-03" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .dateTime
    "yyyy-MM-dd" "yyyy-MM-dd'T'HH:mm:ss" "2024-01-02T12:00:00" "2024-01-01" "2024-01-03" = none ∧
    temporalRun "[Rows/Tag] < [$Expected]" .date .time
    "yyyy-MM-dd" "HH:mm:ss" "12:00:00" "2024-01-01" "2024-01-03" = none ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .date
    "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" "2024-01-01" "2024-01-03" .dayOptional = none := by native_decide

example : temporalRun "[Rows/Tag] == [$Expected]" .dateTime .dateTime
    "yyyy-MM-dd'T'HH:mm:ss" "yyyy-MM-dd'T'HH:mm:ss"
    "2024-01-02T12:00:00" "2024-01-02T12:00:00" "2024-01-02T13:00:00" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .date
    "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" "" "2024-01-02" =
      some (.notFired, ["value 5"]) ∧
    temporalRun "[Rows/Tag] == [$Expected]" .date .date
    "yyyy-MM-dd" "yyyy-MM-dd" "2024-01-02" "bad" "2024-01-02" =
      some (.notFired, []) := by native_decide

private def rangeRun (op leftFormat rightFormat expected first second : String)
    (leftSeparator rightSeparator : Option String := none) :=
  let fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 then
      { field with policy := { kind := .dateRange }, dateRangePolicy := some {
          format := if field.id == 3 then leftFormat else rightFormat
          separator := if field.id == 3 then leftSeparator.getD (if leftFormat.startsWith "dd." then "-" else "/")
            else rightSeparator.getD (if rightFormat.startsWith "dd." then "-" else "/") } }
    else field
  runModel { model with fields } ("[Rows/Tag] " ++ op ++ " [$Expected]") false expected first second

example : rangeRun "==" "dd.MM.yyyy" "yyyy-MM-dd" "2024-01-01/2024-02-01"
    "01.01.2024-01.02.2024" "01.01.2024-01.03.2024" = some (.fired .omission, ["value 9"]) ∧
    rangeRun "!=" "MM" "MM" "01/02" "01/03" "01/02" = some (.fired .omission, ["value 9"]) ∧
    rangeRun "==" "MM-dd" "dd.MM" "01.01-01.02" "01-01/02-01" "01-01/03-01" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : rangeRun "==" "MM" "MM-dd" "01-01/02-01" "01/02" "01/03" = none ∧
    rangeRun "<" "MM" "MM" "01/02" "01/02" "01/03" = none ∧
    rangeRun "==" "MM" "MM" "01/02" "" "01/02" = some (.notFired, ["value 5"]) ∧
    rangeRun "==" "MM" "MM" "01/02" "bad" "01/02" = some (.notFired, []) := by native_decide

example : rangeRun "==" "yyyy" "yyyy" "2024/2025" "2024/2025" "2024/2026" =
      some (.fired .omission, ["value 9"]) ∧
    rangeRun "==" "yyyy-MM" "yyyy-MM" "2024-01/2024-02" "2024-01/2024-02" "2024-01/2024-03" =
      some (.fired .omission, ["value 9"]) ∧
    rangeRun "==" "MM" "MM" "01/02" "0102" "0103" (some "") =
      some (.fired .omission, ["value 9"]) := by native_decide

private def fillOperators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

example : fillOperators.map (fun op =>
    run (op ++ "(Rows/Tag, $Expected)") false .string "keep" "keep" "") =
      [some (.fired .omission, ["value 9"]), some (.notFired, ["value 0"]),
       some (.notFired, ["value 14"]), some (.fired .omission, ["value 9"]),
       some (.notFired, ["value 5"]), some (.fired .omission, ["value 9"]),
       some (.notFired, ["value 5"])] := by native_decide

example : fillOperators.map (fun op =>
    (run (op ++ "(Rows/Tag, $Expected)") false .string "" "" "keep").map (·.2)) =
      [some ["value 0"], some ["value 9"], some ["value 5"], some ["value 0"],
       some ["value 14"], some ["value 9"], some ["value 5"]] := by native_decide

example : run "AtLeastOneFieldFilled(Rows/Tag, $Expected)" false .boolean "true" "bad" "false" =
      some (.notFired, []) ∧
    run "AtLeastOneFieldFilled($Expected, Rows/Tag)" false .boolean "true" "bad" "false" =
      some (.notFired, ["value 14"]) ∧
    run "AllFieldsFilled(Rows/Tag)" = none ∧
    run "AllFieldsFilled(Rows/Tag, Rows/Tag)" = none := by native_decide

private def fillReferences : Option (Bool × Bool) := do
  let parsed ← (parseText .english
    "FieldValuesNotUnique(/Form/Rows*/Tag Having AllFieldsFilled(/Form/Rows/Tag, $/Form/Rows/Tag))").toOption
  let checked ← (lowerCondition model ["Form", "Rows"] false parsed.body).toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (pointers.contains { field := 3, coordinates := [.wildcard] },
    pointers.contains { field := 3, coordinates := [.concrete 2] })

example : fillReferences = some (true, true) := by native_decide

example : [("== 2", "x"), ("!= 1", "x"), ("< 3", "abcd"), ("<= 2", "abcd"),
    ("> 1", "x"), (">= 2", "x")].all (fun (suffix, rejected) =>
    run ("Length(Rows/Tag) " ++ suffix) false .string "x" "ab" rejected ==
      some (.fired .omission, ["value 9"])) = true := by native_decide

example : run "Length(Rows/Tag) + 1 == 3" false .string "x" "ab" "x" =
      some (.fired .omission, ["value 9"]) ∧
    run "3 > Length(Rows/Tag)" false .string "x" "ab" "abcd" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : run "Length(Rows/Tag) == Length($Expected)" false .string "ab" "xy" "z" =
      some (.fired .omission, ["value 9"]) ∧
    (run "Length(Rows/Tag) == Length($Expected)" true .string "ab" "xy" "drop").map (·.2) =
      some ["value drop", "value 5"] ∧
    referencesFor "Length(/Form/Rows/Tag) == Length($/Form/Rows/Tag)" = some (true, true) := by native_decide

example : run "Length(Rows/Tag) == 2" false .string "x" "é" "x" =
      some (.fired .omission, ["value 9"]) ∧
    run "Length(Rows/Tag) == 2" false (.number { scale := 0, signed := true }) "2" "2" "1" = none ∧
    run "Length(Rows/Tag -> Swap) == 2" false .enumeration "keep" "keep" "drop" (some domain) = none ∧
    run "Length([Rows/Tag]) == 2" = none ∧
    run "Length($Expected) == 4" = none := by native_decide

private def constrainedLengthModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with stringPolicy := { maxLength := some 2 } } else field }

example : runModel constrainedLengthModel "Length(Rows/Tag) > 0" false "a" "ab" "long" =
      some (.fired .omission, []) ∧
    runModel { model with fields := model.fields.map fun field =>
        if field.id == 3 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } }
        else field } "Length(Rows/Tag) > 0" false "a" "ab" "x" = none := by native_decide

example : toleranceRanges.all (fun band =>
    run s!"Length(Rows/Tag) * {band} DiffersWithToleranceRange{band} Length($Expected) * {band}"
      false .string "abc" "abcde" "ab" == some (.fired .omission, ["value 9"])) = true ∧
    run "Length(Rows/Tag) < 2.5" false .string "x" "ab" "abc" =
      some (.fired .omission, ["value 9"]) ∧
    run "Length(Rows/Tag) > 0" false .enumeration "keep" "keep" "drop" (some domain) = none := by native_decide

example : [("YearFromDate", "2024"), ("MonthFromDate", "4"), ("QuarterFromDate", "2"),
    ("DayFromDate", "12")].all (fun (operator, expected) =>
    temporalRun s!"{operator}(Rows/Tag) == {expected}" .date .date
      "yyyy-MM-dd" "yyyy-MM-dd" "2024-04-12" "2024-04-12" "2023-01-01" ==
        some (.fired .omission, ["value 9"])) = true ∧
    [("HoursFromTime", "12"), ("MinutesFromTime", "34"), ("SecondsFromTime", "56")].all (fun (operator, expected) =>
    temporalRun s!"{operator}(Rows/Tag) == {expected}" .time .time
      "HH:mm:ss" "HH:mm:ss" "12:34:56" "12:34:56" "01:02:03" ==
        some (.fired .omission, ["value 9"])) = true := by native_decide

example : run "RangeAsNumber(Rows/Tag, 2, 3) == 12" false .string "x12" "a12z" "a45z" =
      some (.fired .omission, ["value 9"]) ∧
    run "RangeAsNumber(Rows/Tag, 2, 3) + 1 == 13" false .string "x12" "a12z" "a45z" =
      some (.fired .omission, ["value 9"]) := by native_decide

example : temporalRun "DayFromDate(Rows/Tag) == 12" .date .date
      "yyyy-MM-dd" "yyyy-MM-dd" "2024-04-12" "2024-04-12" "2023-01-01" .dayOptional =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "HoursFromTime(Rows/Tag) == 12" .date .date
      "HH:mm:ss" "HH:mm:ss" "12:34:56" "12:34:56" "01:02:03" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "YearFromDate(Rows/Tag) == 2024" .time .time
      "yyyy-MM-dd" "yyyy-MM-dd" "2024-04-12" "2024-04-12" "2023-01-01" =
      some (.fired .omission, ["value 9"]) ∧
    temporalRun "YearFromDate(Rows/Tag) == 2024" .date .date
      "HH:mm:ss" "HH:mm:ss" "12:34:56" "12:34:56" "01:02:03" = none ∧
    temporalRun "HoursFromTime(Rows/Tag) == 12" .time .time
      "yyyy-MM-dd" "yyyy-MM-dd" "2024-04-12" "2024-04-12" "2023-01-01" = none := by native_decide

example : temporalRun "MonthFromDate(Rows/Tag) == 4" .date .date
      "MM-dd" "MM-dd" "04-12" "04-12" "01-01" = some (.fired .omission, ["value 9"]) ∧
    temporalRun "YearFromDate(Rows/Tag) == 2024" .date .date
      "MM-dd" "MM-dd" "04-12" "04-12" "01-01" = none ∧
    (temporalRun "YearFromDate(Rows/Tag) == 2024" .date .date
      "MM-dd" "MM-dd" "04-12" "04-12" "01-01" .full (some 2024)).map (·.2) = some ["value 14"] ∧
    dateRun "DayFromDate(Rows/Tag) + 1 == DayFromDate($Expected)" = some (.fired .omission, ["value 9"]) ∧
    (dateRun "DayFromDate(Rows/Tag) > 0" "bad").map (·.2) = some [] := by native_decide

private def componentPointerModel : FlatModel := { model with fields := (model.fields.map fun field =>
  if field.id == 3 then { field with
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field)
  ++ [{ id := 6, groupPath := ["Form", "Rows"], name := "Token", policy := { kind := .string }, repeatableScope := [10] }] }

example : referencesFor "DayFromDate(/Form/Rows/Tag) == DayFromDate($/Form/Rows/Tag)" componentPointerModel "Token" =
      some (true, true) ∧
    referencesFor "RangeAsNumber(/Form/Rows/Tag, 1, 2) == RangeAsNumber($/Form/Rows/Tag, 1, 2)" =
      some (true, true) ∧
    run "RangeAsNumber(Rows/Tag, 2, 3) == RangeAsNumber($Expected, 2, 3)" true .string "a12" "a12" "xro" =
      some (.fired .omission, ["value drop", "value 5"]) := by native_decide

example : run "RangeAsNumber(Rows/Tag, 2, 3) == 0" false .string "x" "aXz" "a12" =
      some (.fired .omission, ["value 9"]) ∧
    run "RangeAsNumber(Rows/Tag, 2, 3) == 0" false .string "x" "a1" "a12" =
      some (.fired .omission, ["value 9"]) ∧
    ["0, 2", "3, 2", "1.0, 2"].all (fun bounds =>
      (run s!"RangeAsNumber(Rows/Tag, {bounds}) > 0").isNone) = true ∧
    run "RangeAsNumber(Rows/N, 1, 2) > 0" = none ∧
    run "YearFromDate(Rows/Tag) == 2024" = none ∧
    run "RangeAsNumber($Expected, 1, 2) > 0" = none ∧
    runModel constrainedLengthModel "RangeAsNumber(Rows/Tag, 1, 2) > 0" false "x" "12" "long" =
      some (.fired .omission, []) := by native_decide


end A12Kernel.Dm.HavingComparisonLocks
