import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingAdmissionLocks
open Lean A12Kernel

private inductive Admission where
  | readerRefused
  | refused (diagnostic : Option KernelStaticDiagnostic)
  | admitted
  deriving BEq, Repr, DecidableEq

private def admission (fixture : FlatModel) (filter : String) : Admission :=
  match parseText .english filter with
  | .error _ => .readerRefused
  | .ok parsed => match lowerHaving parsed.body with
    | .error _ => .readerRefused
    | .ok authored => match elaborateStarFieldPath fixture ["Form"] {
        base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" } with
      | .error _ => .readerRefused
      | .ok source => match elaborateStarHavingCore fixture ["Form"] source authored with
        | .ok _ => .admitted
        | .error error => .refused error.diagnostic?

private def domain : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Swap", tokens := ["drop", "keep"] }] }

private def fixture (kind : FieldKind := .string) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field =>
    if field.id == 3 then { field with
      policy := { kind }
      enumeration := if kind == .enumeration then some domain else none
      dateRangePolicy := if kind == .dateRange then some { format := "yyyy-MM-dd", separator := "/" } else none } else field }

private def kinds : List FieldKind := [.string, .enumeration, .boolean, .confirm,
  .number { scale := 0, signed := true }, .temporal .date TemporalComponents.fullDate,
  .temporal .time (TemporalComponents.ofFormat "HH:mm:ss"), .temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss"), .dateRange]

private def orderings : List String := ["<", "<=", ">", ">="]

private def comparison (reference operator : String) (reverse : Bool := false)
    (literal : String := "keep") : String :=
  if reverse then "\"" ++ literal ++ "\" " ++ operator ++ " " ++ reference
  else reference ++ " " ++ operator ++ " \"" ++ literal ++ "\""

example : kinds.all (fun kind => orderings.all fun operator => [false, true].all fun reverse =>
    admission (fixture kind) (comparison "[Rows/Tag]" operator reverse) ==
      .refused (some .invalidTypeForComparison)) = true := by native_decide

example : ["[Rows/Tag]", "[Rows/Tag -> Swap]"].all (fun reference =>
    orderings.all fun operator => [false, true].all fun reverse =>
      ["keep", "outside-domain"].all fun literal =>
        admission (fixture .enumeration) (comparison reference operator reverse literal) ==
          .refused (some .invalidTypeForComparison)) = true ∧
    admission (fixture .enumeration) "[Rows/Tag] == \"outside-domain\"" =
      .refused (some .invalidStringConstantForEnumComparison) := by native_decide

example : ["[Rows/Tag]", "[/Form/Rows/Tag]"].all (fun reference =>
    [false, true].all fun reverse =>
      HavingFixture.run (comparison reference "==" reverse) == some (.fired .omission, ["value 9"]) &&
      HavingFixture.run (comparison reference "!=" reverse) == some (.notFired, ["value 5"] )) = true := by native_decide

private def preservesReadRefusal (model : FlatModel) (reference : String) : Bool :=
  match admission model (comparison reference "==") with
  | .refused (some diagnostic) => diagnostic != .invalidTypeForComparison &&
      orderings.all fun operator => [false, true].all fun reverse =>
        admission model (comparison reference operator reverse) == .refused (some diagnostic)
  | _ => false

example : ["[Rows/Missing]", "[Rows]", "[$Rows/Tag]"].all
      (preservesReadRefusal (fixture .string)) = true ∧
    preservesReadRefusal (fixture .enumeration) "[Rows/Tag -> Missing]" = true := by native_decide


example : ["<", "=="].all (fun operator =>
    admission (fixture .enumeration) ("[Rows/Tag -> Missing] " ++ operator ++ " [$Expected]") ==
      .refused (some .categoryUnknown)) = true := by native_decide

example : [false, true].all (fun reverse =>
    HavingFixture.run (comparison "[Rows/Tag -> Swap]" "==" reverse) (kind := .enumeration)
      (enumeration := some domain) == some (.notFired, ["value 5"]) &&
    HavingFixture.run (comparison "[Rows/Tag -> Swap]" "!=" reverse) (kind := .enumeration)
      (enumeration := some domain) == some (.fired .omission, ["value 9"])) = true := by native_decide

private def admissionInArms (filter : String) : Bool × Bool :=
  let operation := "Sum(Rows*/N Having " ++ filter ++ ")"
  (((parseText .english (operation ++ " > 0")).toOption.bind fun parsed =>
    (lowerCondition (fixture .string) ["Form"] false parsed.body).toOption).isSome,
  (lowerComputation (fixture .string) .english {
    group := ["Form"], name := "Total", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).isOk)

example : orderings.all (fun operator => [false, true].all fun reverse =>
    admissionInArms (comparison "[Rows/Tag]" operator reverse) == (false, false)) = true ∧
    ["==", "!="].all (fun operator => [false, true].all fun reverse =>
      admissionInArms (comparison "[Rows/Tag]" operator reverse) == (true, true)) = true := by native_decide


example : preservesReadRefusal { (fixture .string) with fields := (fixture .string).fields.map fun field =>
    if field.id == 3 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field } "[Rows/Tag]" = true ∧
    orderings.all (fun operator =>
      admission (fixture .string) (comparison "[$Expected]" operator) ==
        .refused (some .invalidTypeForComparison)) = true ∧
    admission (fixture .string) "[$Expected] == \"keep\" And FieldFilled(Rows/N)" = .admitted ∧
    admission (fixture .string) "[$Expected] == \"keep\"" =
      .refused (some .noIterationForWildcard) := by native_decide


private def stringExpressions : List (String × String × String) := [
  ("[Rows/Tag] + \"!\"", "keep!", "9"),
  ("RangeAsString(Rows/Tag,1,1)", "k", "9"),
  ("FieldValueAsString(Rows/N)", "2", "2")]

example : stringExpressions.all (fun (source, literal, _) =>
    orderings.all fun operator => [false, true].all fun reverse =>
      admission (fixture .string) (comparison source operator reverse literal) ==
        .refused (some .invalidTypeForComparison)) = true ∧
    stringExpressions.all (fun (source, literal, amount) => [false, true].all fun reverse =>
      HavingFixture.runModel (fixture .string) (comparison source "==" reverse literal) false
        "keep" "keep" "drop" (ruleExpected := amount) == some (.fired .omission, ["value " ++ amount])) = true := by native_decide

example : orderings.all (fun operator =>
    admission (fixture .string) (comparison "\"a\" + \"b\"" operator false "ab") ==
      .refused (some .invalidTypeForComparison)) = true ∧
    preservesReadRefusal (fixture .string) "RangeAsString(Missing,1,1)" = true := by native_decide

example : ["\"a\" + \"b\" == \"ab\"", "\"a\" + \"b\" != \"c\" + \"d\"",
    "{\"a\" + \"b\"} == {\"ab\"}"].all (fun comparison =>
      HavingFixture.runModel (fixture .string) (comparison ++ " And FieldFilled(Rows/N)") false
        "keep" "keep" "drop" (ruleExpected := "14") == some (.fired .omission, ["value 14"])) = true ∧
    admission (fixture .string) "\"a\" + \"b\" == \"ab\"" =
      .refused (some .noIterationForWildcard) := by native_decide

private def stringCertificate (left : StringExpr HavingStringSource) : Bool :=
  let source : HavingStringComparison := { operator := .equal, left, right := .literal "ab" }
  source.wellFormed (fixture .string) [10] []

example : stringCertificate (.literal "a") = false ∧
    stringCertificate (.concat (.literal "a") (.literal "b")) = true ∧
    stringCertificate (.concat (.field (.field { origin := .inner, field := 3 })) (.literal "b")) = true := by native_decide

private def booleanComparison (operator literal : String) (reverse : Bool) : String :=
  if reverse then literal ++ " " ++ operator ++ " [Rows/Tag]"
  else "[Rows/Tag] " ++ operator ++ " " ++ literal

example : kinds.all (fun kind => orderings.all fun operator =>
    ["True", "False"].all fun literal => [false, true].all fun reverse =>
      admission (fixture kind) (booleanComparison operator literal reverse) ==
        .refused (some .invalidTypeForComparison)) = true ∧
    [false, true].all (fun reverse =>
      HavingFixture.run (booleanComparison "==" "True" reverse) (kind := .boolean)
        (expected := "false") (first := "true") (second := "false") ==
          some (.fired .omission, ["value 9"]) &&
      HavingFixture.run (booleanComparison "==" "True" reverse) (kind := .confirm)
        (expected := "true") (first := "true") (second := "") ==
          some (.fired .omission, ["value 9"])) = true := by native_decide


example : ["Missing", "Swap"].all (fun category => ("==" :: "!=" :: orderings).all fun operator =>
    ["True", "False"].all fun literal => [false, true].all fun reverse =>
      let reference := "[Rows/Tag -> " ++ category ++ "]"
      let filter := if reverse then literal ++ " " ++ operator ++ " " ++ reference
        else reference ++ " " ++ operator ++ " " ++ literal
      admission (fixture .enumeration) filter == .refused (some (
        if category == "Missing" then .categoryUnknown
        else if operator == "==" || operator == "!=" then .invalidCompareToEnumOrString
        else .invalidTypeForComparison))) = true := by native_decide

end A12Kernel.Dm.HavingAdmissionLocks
