import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # Computation predicate guard composition

The reader and scheduler must preserve target binding and phase-specific reads after a predicate
is admitted. Malformed seeds separate fresh computed overlays from immutable source reads.
-/

namespace A12Kernel.Dm.ComputationPredicateGuardLocks

private def model (kind : FieldKind := .boolean)
    (listKind : FieldKind := .number { scale := 0, signed := true }) : FlatModel := {
  fields := [
    { id := 1, name := "Flag", groupPath := ["Form"], policy := { kind } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "A", groupPath := ["Form", "Left"], policy := { kind := listKind } },
    { id := 4, name := "B", groupPath := ["Form", "Right"], policy := { kind := listKind } }] }

private def run (guard : String) (kind : FieldKind) (flag : RawCell)
    (left right : RawCell := .empty) (producer : Bool := false)
    (producerOperation : String := "True")
    (listKind : FieldKind := .number { scale := 0, signed := true }) : Option (List String) := do
  let model := model kind listKind
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let cell (id : FieldId) (raw : RawCell) : Option ClassifiedCellInput :=
    match raw with
    | .empty => none
    | raw =>
        let stored := match raw with
          | .parsed (.num value) => toString value.num
          | .parsed (.bool value) | .parsed (.conf value) => if value then "true" else "false"
          | .parsed (.str value) | .parsed (.enum value) => value
          | .presentEmpty => ""
          | _ => "bad"
        some { address := { field := id, path := [] }, raw, stored }
  let input ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := ([cell 1 flag, cell 2 (.parsed (.num 9)), cell 3 left, cell 4 right].filterMap id) }).toOption
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := "../Out"
    commonPrecondition := some guard, alternatives := [{ precondition := none, operation := "2" }]
    errorCodesToSuppress := [] }
  let produce : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Flag"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := producerOperation }]
    errorCodesToSuppress := [] }
  let authored := [consumer] ++ if producer then [produce] else []
  let lowered ← authored.mapM fun definition => (lowerComputation model .english definition).toOption
  let results ← (runComputations world prepared input (lowered.map (·.2))).toOption
  pure (results.map (·.outcome))


example : run "[Flag] != True" .boolean .empty = some ["cleared"] ∧
    run "[Flag] != True" .confirm .empty = some ["value 2"] ∧
    run "[Flag] == False" .confirm .empty = none := by native_decide

example : run "[Flag] == True" .boolean (.rejected .booleanToken) .empty .empty true =
    some ["value true", "value 2"] := by native_decide

example :
    ["AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled", "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"].map
      (fun name => run (name ++ "(Left, Right)") .boolean .empty .empty (.rejected .malformed)) =
      [some ["cleared"], some ["cleared"], some ["value 2"], some ["value 2"], some ["value 2"]] := by
  native_decide

example : run "AtLeastOneGroupFilled(Left/A, Right)" .boolean .empty (.rejected .malformed)
    (.parsed (.num 1)) = some ["cleared"] ∧
    run "AtLeastOneGroupFilled(Right, Left/A)" .boolean .empty (.rejected .malformed)
      (.parsed (.num 1)) = some ["value 2"] := by native_decide

private def numericKind : FieldKind := .number { scale := 0, signed := true }

example : run "AtLeastOneFieldValueIncludedInValueList(Left/A, Right/B In Flag)" numericKind
    (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["value 2"] ∧
    run "AtLeastOneFieldValueIncludedInValueList(Right/B, Left/A In Flag)" numericKind
      (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["cleared"] := by native_decide

example : run "NoFieldValueIncludedInValueList(Left/A, Right/B In Flag)" numericKind
    (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["cleared"] ∧
    run "NotAllFieldValuesIncludedInValueList(Left/A, Right/B In Flag)" numericKind
      (.parsed (.num 9)) (.parsed (.num 1)) (.rejected .malformed) = some ["value 2"] := by native_decide

example : run "AtLeastOneFieldValueIncludedInValueList(Left/A In Flag)" numericKind
    (.rejected .malformed) (.parsed (.num 1)) .empty true "1" = some ["value 1", "value 2"] := by
  native_decide

/-- Scalar membership is calibrated on the same family grid as plural membership, but keeps
its eager member reads even with an empty subject. -/
example : run "FieldValueIncludedInValueList(Flag, 1, 2)" numericKind (.parsed (.num 1)) =
    some ["value 2"] ∧
    run "FieldValueNotIncludedInValueList(Flag, 1, 2)" numericKind (.parsed (.num 3)) =
      some ["value 2"] ∧
    run "FieldValueIncludedInValueList(Flag, [Left/A], [Right/B])" numericKind
      (.parsed (.num 1)) (.parsed (.num 1)) (.rejected .malformed) = some ["cleared"] ∧
    run "FieldValueNotIncludedInValueList(Flag, [Left/A])" numericKind
      .empty (.rejected .malformed) = some ["cleared"] ∧
    run "FieldValueIncludedInValueList(Flag, \"x\", \"y\")" .string (.parsed (.str "x")) =
      some ["value 2"] := by native_decide

example : run "FieldValueIncludedInValueList([Flag], 1)" numericKind (.parsed (.num 1)) = none ∧
    run "FieldValueIncludedInValueList(Flag, Left/A)" numericKind (.parsed (.num 1)) = none ∧
    run "FieldValueIncludedInValueList(Flag, 1.0)" numericKind (.parsed (.num 1)) = none ∧
    run "FieldValueIncludedInValueList(Flag, [Flag])" numericKind (.parsed (.num 1)) = none := by
  native_decide

private def capturedMembership (enumeration : Bool) (guard : String) (selection : String := "2")
    (keepProducer : Bool := false) :
    Option (List String) := do
  let source : FlatFieldDecl := {
    id := 1, name := "A", groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := if enumeration then .enumeration else .string }
    enumeration := if enumeration then some { storedTokens := ["A", "B"] } else none }
  let model : FlatModel := {
    fields := [source,
      { source with id := 2, name := "B", groupPath := ["Form"], repeatableScope := [] },
      { id := 3, name := "Keep", groupPath := ["Form", "Rows"], repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 4, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 5, name := "After", groupPath := ["Form", "Rows"], repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
  let row := fun a keep => Lean.Json.mkObj [("A", Lean.Json.str a), ("Keep", .str keep), ("Out", "9"), ("After", "9")]
  let input ← (readDocument {
      flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Lean.Json.mkObj [("Form", Lean.Json.mkObj [("B", "B"), ("Rows", .arr #[
      row "A" "1", row "B" selection])])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let (_, step) ← (lowerComputation model .english {
    group := ["Form"], name := "Member", targetRelPath := "../Rows/Out"
    commonPrecondition := some guard, alternatives := [{ precondition := none, operation := "1" }]
    errorCodesToSuppress := [] }).toOption
  let (_, dependent) ← (lowerComputation model .english {
    group := ["Form"], name := "Dependent", targetRelPath := "../Rows/After"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "[Rows/Out] + 1" }]
    errorCodesToSuppress := [] }).toOption
  let producer : DmComputation := {
    group := ["Form"], name := "KeepProducer", targetRelPath := "../Rows/Keep"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "2" }]
    errorCodesToSuppress := [] }
  let producers ← (if keepProducer then [producer] else []).mapM fun declaration =>
    (lowerComputation model .english declaration).toOption.map (·.2)
  pure ((← (runComputations world prepared checked ([step, dependent] ++ producers)).toOption).map (·.outcome))

example : [false, true].all (fun enumeration =>
    ["Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep] In B",
      "B In Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep]",
      "Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep] In \"B\""].all fun operands =>
      let guard := s!"AtLeastOneFieldValueIncludedInValueList({operands})"
      capturedMembership enumeration guard == some ["cleared", "value 1", "value 1", "value 2"] &&
      capturedMembership enumeration guard "bad" == some ["cleared", "cleared", "value 1", "cleared"] &&
      capturedMembership enumeration guard "0" == some ["cleared", "cleared", "value 1", "value 1"]) := by native_decide

example : [false, true].all (fun enumeration =>
    ["Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep] In B",
      "B In Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep]",
      "Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep] In \"B\""].all fun operands =>
      let guard := s!"AtLeastOneFieldValueIncludedInValueList({operands})"
      ["0", "bad"].all fun selection => capturedMembership enumeration guard selection true ==
        some ["value 2", "value 2", "value 1", "value 1", "value 2", "value 2"]) = true := by native_decide

private def categoryDomain : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
  categories := [{ name := "Kind", tokens := ["X", "Y"] }] }

private def categoryModel : FlatModel := {
  fields := [
    { id := 1, name := "Code", groupPath := ["Form"], policy := { kind := .enumeration }, enumeration := some categoryDomain },
    { id := 2, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration }, enumeration := some categoryDomain },
    { id := 3, name := "Qty", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def categoryRun (operation : String) (guard : Option String := none)
    (fresh : Bool := false) (rowTarget : Bool := false) (secondCode : String := "B") : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler categoryModel).toOption
  let dm : DmModel := { flat := categoryModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Code", .str "A"), ("Out", .str "0"), ("Rows", .arr #[
      Lean.Json.mkObj [("Code", .str "A"), ("Qty", .str "2"), ("Out", .str "0")],
      Lean.Json.mkObj [("Code", .str secondCode), ("Qty", .str "7"), ("Out", .str "0")]])])])).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := if rowTarget then "../Rows/Out" else "../Out", commonPrecondition := guard,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let producer : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Rows/Code", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "\"A\"" }], errorCodesToSuppress := [] }
  let steps ← (consumer :: if fresh then [producer] else []).mapM fun definition =>
    (lowerComputation categoryModel .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

example : categoryModel.validate.isOk = true := by native_decide
example : categoryRun "1" (some "[Code -> Kind] == \"X\"") = some ["value 1"] := by native_decide
example : categoryRun "Sum(Rows*/Qty Having [Rows/Code -> Kind] == \"X\")" = some ["value 2"] := by native_decide
example : categoryRun "NumberOfFilledFields(Rows*/Qty Having [Rows/Code -> Kind] == \"Y\")" = some ["value 1"] := by native_decide
example : categoryRun "Sum(Rows*/Qty Having [Rows/Code -> Kind] == \"X\")" none true =
    some ["value A", "value 9"] := by native_decide

example : categoryRun "Sum(Rows*/Qty Having \"X\" == [Rows/Code -> Kind])" =
    some ["value 2"] ∧
    categoryRun "Sum(Rows*/Qty Having \"X\" != [Rows/Code -> Kind])" =
      some ["value 7"] := by native_decide

example : ["[Rows/Code -> Kind] == \"A\"", "[Rows/Code -> Missing] == \"X\"",
    "[Rows/Qty -> Kind] == \"X\""].all (fun predicate =>
      (categoryRun s!"Sum(Rows*/Qty Having {predicate})").isNone) = true := by native_decide

example : categoryRun "Sum(Rows*/Qty Having [Rows/Code] == \"A\")" = some ["value 2"] ∧
    categoryRun "Sum(Rows*/Qty Having [Rows/Code -> Kind] == \"X\")" none false false "bad" =
      some ["cleared"] ∧
    categoryRun "Sum(Rows*/Qty Having [Rows/Code -> Kind] == \"X\")" none false false "" =
      some ["value 2"] := by native_decide

example : categoryRun "Sum(Rows*/Qty Having ([Rows/Code -> Kind] == \"X\" Or [$Rows/Code -> Kind] == \"Y\"))"
    none false true = some ["value 2", "value 9"] ∧
    categoryRun "1" (some "[Rows/Code -> Kind] == \"X\"") false true =
      some ["value 1", "cleared"] := by native_decide

private def categoryCertificate (literal : String) (projectionRef : EnumerationProjectionRef)
    (origin : HavingOrigin) (outerLevels : List RepeatableLevel) : Option Bool := do
  let declaration ← categoryModel.fields[1]?
  let .compare (.enumeration _ operand _) ←
    (elaborateEnumerationCore declaration .equal (.category "Kind") "X").toOption | none
  let condition := CorrelatedHaving.compareStringLiteral .equal
    { origin, operand := .enumeration { operand with projectionRef } } literal
  pure (condition.wellFormedForEnvironments categoryModel [10] outerLevels)

example : categoryCertificate "X" (.category "Kind") .inner [] = some true ∧
    categoryCertificate "A" (.category "Kind") .inner [] = some false ∧
    categoryCertificate "X" .stored .inner [] = some false ∧
    categoryCertificate "A" .stored .inner [] = some false ∧
    categoryCertificate "X" (.category "Kind") .outer [] = some false ∧
    categoryCertificate "X" (.category "Kind") .outer [10] = some true := by native_decide

example : CorrelationElabError.diagnostic?
    (.text (.enumerationOperand ["Form", "Rows", "Code"] (.invalidLiteral "A"))) =
      some .invalidStringConstantForEnumComparison := rfl

private def categoryPointers : Option (List MessagePointer) := do
  let leaf (origin : HavingOrigin) := SurfaceCorrelatedHaving.compareStrings .equal
    { origin, field := { base := .absolute, groups := ["Form", "Rows"], field := "Code" }
      projectionRef := .category "Kind" } "X"
  let source ← (elaborateTokenValueCountSource categoryModel ["Form", "Rows"] "A" {
    first := .starHaving
      { base := .absolute, groups := [{ name := "Form" }, { name := "Rows", starred := true }]
        field := "Code" } .stored (.and (leaf .inner) (leaf .outer))
    rest := [] }).toOption
  (source.referencePointers [(10, 2)]).toOption

example : categoryPointers = some [
    { field := 2, coordinates := [.wildcard] },
    { field := 2, coordinates := [.wildcard] },
    { field := 2, coordinates := [.concrete 2] }] := by native_decide

private def categoryReadError (kind : FieldKind) (projectionRef : EnumerationProjectionRef)
    (stringValueMode : StringValueMode := .evaluated) : Option CorrelationElabError :=
  let model := { categoryModel with fields := categoryModel.fields.map fun declaration =>
    if declaration.id == 2 then
      { declaration with
        policy := { kind }
        enumeration := none
        stringValueMode := stringValueMode
        stringPolicy := { lineBreaksPermitted := kind == .string } }
    else declaration }
  let checked : Except CorrelationElabError CorrelatedHaving := do
    let star ← (elaborateStarFieldPath model ["Form"]
      { base := .absolute, groups := [{ name := "Form" }, { name := "Rows", starred := true }]
        field := "Qty" }).mapError fun _ => .incoherentCore
    pure (← elaborateStarHavingCore model ["Form"] star (.compareStrings .equal
      { origin := .inner, field := { base := .absolute, groups := ["Form", "Rows"], field := "Code" }, projectionRef }
      "X")).condition
  match checked with | .error error => some error | .ok _ => none

example : categoryReadError .string (.category "Kind") .raw =
    some (.resolve (.categoryReadOfNonEnumeration ["Form", "Rows", "Code"])) ∧
    categoryReadError (.temporal .date { TemporalComponents.fullDate with day := false }) (.category "Kind") =
      some (.resolve (.categoryReadOfNonEnumeration ["Form", "Rows", "Code"])) ∧
    categoryReadError .string .stored .raw =
      some (.resolve (.rawFieldValueRead ["Form", "Rows", "Code"])) ∧
    categoryReadError .string .stored = none := by native_decide

example : run "[Flag] PatternMatched \"[0-9]+\"" .string (.parsed (.str "123")) = some ["value 2"] ∧
    run "[Flag] PatternViolated \"[0-9]+\"" .string (.parsed (.str "123")) = some ["cleared"] ∧
    run "[Flag] PatternViolated {\"[0-9]+\"}" .string (.parsed (.str "x123")) = some ["value 2"] ∧
    run "[Flag] PatternMatched \"[0-9]+\"" .string (.rejected .malformed) .empty .empty true "\"123\"" =
      some ["value 123", "value 2"] := by native_decide

example : run "[Flag] PatternMatched {{\"[0-9]+\"}}" .string (.parsed (.str "123")) = some ["value 2"] := by native_decide

example : ["{[Flag]} PatternMatched \"[0-9]+\"", "[Flag] + \"x\" PatternMatched \"[0-9]+\"",
    "[Flag] PatternMatched [Flag]"].all (fun guard =>
      (run guard .string (.parsed (.str "123"))).isNone) := by native_decide

private def patternRows (second : String) (fresh : Bool := false)
    (alternatives : Bool := false) : Option (List String) := do
  let model : FlatModel := {
    fields := [
      { id := 1, groupPath := ["Form", "Rows"], name := "Flag", repeatableScope := [10]
        policy := { kind := .string }, stringPolicy := { maxLength := some 3 } },
      { id := 2, groupPath := ["Form", "Rows"], name := "Out", repeatableScope := [10]
        policy := { kind := numericKind } },
      { id := 3, groupPath := ["Form", "Rows"], name := "After", repeatableScope := [10]
        policy := { kind := numericKind } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let row (flag : String) := Lean.Json.mkObj [("Flag", .str flag), ("Out", .str "9"), ("After", .str "9")]
  let input ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Rows", .arr #[row "123", row second])])])).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let matched := "[Rows/Flag] PatternMatched \"[0-9]+\""
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := "../Rows/Out"
    commonPrecondition := if alternatives then none else some matched
    alternatives := if alternatives then [
      { precondition := some matched, operation := "1" },
      { precondition := some "[Rows/Flag] PatternViolated \"[0-9]+\"", operation := "2" }]
      else [{ precondition := none, operation := "1" }]
    errorCodesToSuppress := [] }
  let dependent : DmComputation := {
    name := "Dependent", group := ["Form"], targetRelPath := "../Rows/After"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "[Rows/Out] + 1" }]
    errorCodesToSuppress := [] }
  let producer : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Rows/Flag"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "\"123\"" }]
    errorCodesToSuppress := [] }
  let steps ← ([consumer, dependent] ++ if fresh then [producer] else []).mapM fun definition =>
    (lowerComputation model .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

example : patternRows "x" = some ["value 1", "cleared", "value 2", "value 1"] ∧
    patternRows "long" = some ["value 1", "cleared", "value 2", "cleared"] ∧
    patternRows "long" true = some ["value 123", "value 1", "value 1", "value 2", "value 2"] ∧
    patternRows "x" false true = some ["value 1", "value 2", "value 2", "value 3"] := by native_decide

example : ["FirstFilledValue(Flag,Left/A) == \"a\"", "\"a\" == FirstFilledValue(Flag,Left/A)",
    "FirstFilledValue(Flag,Left/A) == FirstFilledValue(Left/A,Flag)"].all (fun guard =>
      run guard .string .empty (.parsed (.str "a")) (listKind := .string) == some ["value 2"]) = true := by native_decide

example : run "FirstFilledValue(Flag,Left/A) != \"a\"" .string .empty .empty
      (listKind := .string) = some ["cleared"] ∧
    run "FirstFilledValue(Flag,Left/A) == \"a\"" .string (.parsed (.str "a")) (.rejected .malformed)
      (listKind := .string) = some ["value 2"] ∧
    run "FirstFilledValue(Flag,Left/A) == \"a\"" .string (.rejected .malformed) (.parsed (.str "a"))
      .empty true "\"a\"" (listKind := .string) = some ["value a", "value 2"] := by native_decide

private def membershipAdmissionModel : FlatModel := {
  fields := [
    { id := 1, name := "N", groupPath := ["Form"], policy := { kind := numericKind } },
    { id := 2, name := "M", groupPath := ["Form"], policy := { kind := numericKind } },
    { id := 3, name := "Text", groupPath := ["Form"], policy := { kind := .string } },
    { id := 4, name := "Other", groupPath := ["Form"], policy := { kind := .string } },
    { id := 5, name := "N", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := numericKind } },
    { id := 6, name := "Value", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, customType := some { name := "Loose" } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def membershipAdmission (arguments : String) : Option String := do
  let parsed ← (parseText .english
    ("AtLeastOneFieldValueIncludedInValueList(" ++ arguments ++ ")")).toOption
  let .predicate source ← (lowerGuard membershipAdmissionModel ["Form"] false parsed.body).toOption | none
  match membershipAdmissionModel.elaborateComputationPredicate ["Form"] ["Form"] source with
  | .ok _ => some "admitted"
  | .error (.token error) => error.diagnostic?.map (·.kernelCode)
  | .error _ => none

example : membershipAdmissionModel.validate.isOk = true ∧
    membershipAdmission "N In M" = some "admitted" ∧
    membershipAdmission "Text In Other" = some "admitted" := by native_decide

/- Keep the competing-defect twins in both orders: the retained Kernel static matrix at
docs/sources/domain-ingestion-probes.md#src-membership-read-order-k13 distinguishes
per-operand binding from delayed whole-list checking, including Number-to-token fallback. -/
example : ([
    ("N In Missing", .invalidEntity),
    ("N In Rows/N", .noWildcard),
    ("N In Missing,Rows/N", .invalidEntity),
    ("N In Rows/N,Missing", .noWildcard),
    ("N,N In Missing", .invalidEntity),
    ("N In Text", .varyingTypesNotAllowed),
    ("Rows/N In Missing", .noWildcard),
    ("N In Rows,Missing", .noWildcard),
    ("N In Missing,Rows", .invalidEntity),
    ("Text In Rows/Value,Missing", .noWildcard),
    ("Text In Missing,Rows/Value", .invalidEntity)] : List (String × KernelStaticDiagnostic)).all
    (fun (arguments, expected) => membershipAdmission arguments == some expected.kernelCode) = true := by
  native_decide

end A12Kernel.Dm.ComputationPredicateGuardLocks
