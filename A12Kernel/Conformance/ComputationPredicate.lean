import A12Kernel.Elaboration.ComputationPredicate

namespace A12Kernel.Conformance.ComputationPredicate

private def model (kind : FieldKind) (repeated : Bool) : FlatModel := {
  fields := [
    { id := 1, name := "A", groupPath := ["Form", "Rows"], policy := { kind },
      repeatableScope := if repeated then [10] else [] },
    { id := 2, name := "B", groupPath := ["Form", "Rows"], policy := { kind },
      repeatableScope := if repeated then [10] else [] }]
  repeatableGroups := if repeated then [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] else [] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field }

private def numberSource : SurfaceComputationPredicate := .entityValueList {
  quantifier := .atLeastOne, fields := { first := .field (path "A"), rest := [] },
  values := { first := .field (path "B"), rest := [] } }

private def literalSource : SurfaceComputationPredicate := .tokenLiteralValueList {
  quantifier := .atLeastOne, fields := { first := .field (path "A"), rest := [] }, values := ["x"] }

private def number : FieldKind := .number { scale := 0, signed := true }

private def context (kind : FieldKind) (left right : RawCell) : ScalarComputationContext :=
  let read := fun id => formalCheck { kind } (if id == 1 then left else right)
  { read
    row := [(10, 1)]
    addressed := some {
      document := { rawCells := fun _ => none, instantiatedRows := [] }
      read := fun _ => read } }

private def run (kind : FieldKind) (repeated : Bool) (source : SurfaceComputationPredicate)
    (context : ScalarComputationContext) : Option ComputationConditionResult := do
  let checked ← ((model kind repeated).elaborateComputationPredicate ["Form"] ["Form", "Rows"] source).toOption
  (checked.evalChecked context).toOption

example : run number false numberSource (context number (.parsed (.num 3)) (.parsed (.num 3))) = some .holds ∧
    run number true numberSource (context number (.parsed (.num 3)) (.parsed (.num 3))) = some .holds := by
  native_decide

example : run .string false literalSource (context .string (.parsed (.str "x")) .empty) = some .holds ∧
    run .string false literalSource (context .string (.rejected .malformed) .empty) = some (.poison .malformed) := by
  native_decide

example : ((model number true).elaborateComputationPredicate ["Form"] ["Form"] numberSource).isOk = false := by
  native_decide

example : run number false numberSource { read := fun _ => formalCheck { kind := number } .empty } = some .notTrue := by
  native_decide

private def star (field : String) : SurfaceFieldEntitySource := {
  first := .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field }
  rest := [] }

private def starSource : SurfaceComputationPredicate := .entityValueList {
  quantifier := .atLeastOne, fields := star "A", values := star "B" }

example : run number true starSource { read := fun _ => formalCheck { kind := number } .empty } = none := by
  native_decide

private def memberValue (kind : FieldKind) (isMember : Bool) : RawCell :=
  match kind with
  | .number _ => .parsed (.num (if isMember then 7 else 3))
  | .string => .parsed (.str (if isMember then "member" else "other"))
  | _ => .empty

private def starredContext (kind : FieldKind) (secondRow : Bool) : ScalarComputationContext := {
  read := fun _ => formalCheck { kind } (.rejected .malformed)
  addressed := some {
    document := {
      rawCells := fun _ => none
      instantiatedRows := [{ group := 10, path := [1] }] ++
        if secondRow then [{ group := 10, path := [2] }] else [] }
    read := fun environment field =>
      let raw := if field == 1 then memberValue kind (environment.contains (10, 2))
        else if environment.contains (10, 1) then memberValue kind true else .empty
      formalCheck { kind } raw } }

example : run number true starSource (starredContext number true) = some .holds ∧
    run number true starSource (starredContext number false) = some .notTrue ∧
    run .string true starSource (starredContext .string true) = some .holds ∧
    run .string true starSource (starredContext .string false) = some .notTrue := by
  native_decide

private def footprint : Option (Bool × Bool × Bool × Bool) := do
  let checked ← ((model number true).elaborateComputationPredicate ["Form"] ["Form", "Rows"] numberSource).toOption
  pure (checked.referencesField 1, checked.referencesField 2, checked.rowBoundBool [], checked.rowBoundBool [10])

example : footprint = some (true, true, false, true) := by native_decide

private def noSource : SurfaceComputationPredicate := .entityValueList {
  quantifier := .no, fields := { first := .field (path "A"), rest := [] },
  values := { first := .field (path "B"), rest := [] } }

/-- The retained no-members-invalid-subject row separates No from AtLeastOne's empty-member prepass. -/
example : run number false noSource (context number (.rejected .malformed) .empty) =
    some (.poison .malformed) ∧
    run number false numberSource (context number (.rejected .malformed) .empty) =
    some .notTrue := by
  native_decide

private def scalarSource (op : ValueListMembershipOp) : SurfaceComputationPredicate :=
  .scalarMembership op (.direct (path "A")) (.fields [.direct (path "B")])

example : [false, true].all (fun repeated =>
    run number repeated (scalarSource .included)
      (context number (.parsed (.num 3)) (.parsed (.num 3))) == some .holds &&
    run number repeated (scalarSource .included)
      (context number (.rejected .malformed) .empty) == some (.poison .malformed) &&
    run .string repeated (scalarSource .notIncluded)
      (context .string .empty (.rejected .malformed)) == some (.poison .malformed)) := by
  native_decide

private def filteredRun (kind : FieldKind) (operator : ValueListQuantifier)
    (badFilter : Nat) (membersFiltered : Bool := false) : Option ComputationConditionResult := do
  let model : FlatModel := {
    fields := [
      { id := 3, name := "Member", groupPath := ["Form"], policy := { kind } },
      { id := 1, name := "A", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind } },
      { id := 2, name := "Keep", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
  let starredPath : SurfaceStarFieldPath := {
    base := .absolute, groups := [{ name := "Form" }, { name := "Rows", starred := true }], field := "A" }
  let filtered : SurfaceFieldEntitySource := {
    first := .starHaving starredPath (.compareStrings .equal { origin := .inner, field := path "Keep" } "y")
    rest := [] }
  let member : SurfaceFieldEntitySource := {
    first := .field { base := .absolute, groups := ["Form"], field := "Member" }, rest := [] }
  let checked ← (model.elaborateComputationPredicate ["Form"] ["Form"] (.entityValueList {
    quantifier := operator, fields := if membersFiltered then member else filtered,
    values := if membersFiltered then filtered else member })).toOption
  let read := fun environment field =>
    if field == 2 then formalCheck { kind := .string } (.parsed (.str "n"))
    else formalCheck { kind } (if field == 3 then memberValue kind true
      else if environment.contains (10, 3) then .rejected .malformed
      else memberValue kind (environment.contains (10, 1)))
  let context : ScalarComputationContext := {
    read := read []
    addressed := some {
      document := {
        rawCells := fun _ => none
        instantiatedRows := [1, 2, 3].map fun row => { group := 10, path := [row] } }
      read } }
  let filterRead := fun environment _ => formalCheck { kind := .string }
    (if environment.contains (10, badFilter) then .rejected .declaredConstraint else .parsed (.str "y"))
  (checked.evalChecked context (some filterRead)).toOption

/-- Kernel membership grid: the prefetched successor is reached, its later filter is not;
member collection remains exhaustive and uses a different continuation from subject search. -/
example : [number, FieldKind.string].all (fun kind =>
    filteredRun kind .atLeastOne 3 == some .holds &&
    filteredRun kind .atLeastOne 2 == some (.poison .declaredConstraint) &&
    filteredRun kind .notAll 0 == some .holds &&
    filteredRun kind .notAll 3 == some (.poison .declaredConstraint) &&
    filteredRun kind .atLeastOne 0 true == some (.poison .malformed)) := by native_decide

private def pattern (op : StringPatternOp) : SurfaceComputationPredicate :=
  .pattern { op, field := path "A", source := "[0-9]+" }

example : [false, true].all (fun repeated =>
    run .string repeated (pattern .matched) (context .string (.parsed (.str "123")) .empty) == some .holds &&
    run .string repeated (pattern .violated) (context .string (.parsed (.str "123")) .empty) == some .notTrue &&
    run .string repeated (pattern .matched) (context .string (.parsed (.str "x123")) .empty) == some .notTrue &&
    run .string repeated (pattern .violated) (context .string (.parsed (.str "x123")) .empty) == some .holds) := by native_decide

example : [StringPatternOp.matched, .violated].all (fun op =>
    run .string true (pattern op) (context .string .empty .empty) == some .notTrue &&
    run .string true (pattern op) (context .string .presentEmpty .empty) == some .notTrue &&
    run .string true (pattern op) (context .string (.rejected .malformed) .empty) == some (.poison .malformed) &&
    (run number true (pattern op) (context number (.parsed (.num 123)) .empty)).isNone) := by native_decide

example : (((model .string true).elaborateComputationPredicate ["Form"] ["Form", "Rows"]
    (pattern .matched)).toOption.map fun checked =>
      (checked.referencesField 1, checked.referencesField 2, checked.rowBoundBool [10], checked.rowBoundBool [])) =
    some (true, false, true, false) := by native_decide

private def patternCompiler : StringPatternCompiler := fun source =>
  if source == "x" then .compiled (· == "x")
  else if source == "" then .compiled String.isEmpty
  else if source == "x++" then .compiled (fun text => !text.isEmpty && text.toList.all (· == 'x'))
  else .rejected

private def hostPattern (op : StringPatternOp) (source : String) :=
  (model .string true).elaborateComputationPredicate ["Form"] ["Form", "Rows"]
    (.pattern { op, field := path "A", source }) patternCompiler

example : ((hostPattern .matched "x").toOption.bind fun checked =>
    (checked.evalChecked (context .string (.parsed (.str "x")) .empty)).toOption) = some .holds := by native_decide

example : [StringPatternOp.matched, .violated].all (fun op =>
    [RawCell.parsed (.str "x"), .empty].all fun cell =>
      match hostPattern op "" with
      | .ok checked => match checked.evalChecked (context .string cell .empty) with
        | .error .valueFailure => true
        | _ => false
      | .error _ => false) = true := by native_decide

example : ((match hostPattern .matched "*" with
    | .error (.pattern (.pattern .javaSyntax)) => true | _ => false) : Bool) = true ∧
    ((match hostPattern .matched "x++" with
    | .error (.pattern (.pattern .kernelRestriction)) => true | _ => false) : Bool) = true := by native_decide

private def patternProfile (raw custom : Bool) :
    Except ComputationPredicateElabError (Option ComputationConditionResult) := do
  let fixture := model .string true
  let fixture : FlatModel := { fixture with fields := fixture.fields.map fun field =>
    if field.id == 1 then { field with
      stringValueMode := if raw then .raw else .evaluated
      stringPolicy := { lineBreaksPermitted := raw }
      customType := if custom then some { name := "HostType" } else none }
    else field }
  let checked ← fixture.elaborateComputationPredicate ["Form"] ["Form", "Rows"] (pattern .matched)
  pure (checked.evalChecked (context .string (.parsed (.str "123")) .empty)).toOption

example : ((match patternProfile true false with
    | .error (.pattern (.field (.resolve (.rawFieldValueRead _)))) => true | _ => false) : Bool) = true ∧
    (patternProfile false true).toOption = some (some .holds) := by native_decide

private def firstToken (left right : SurfaceTokenComparisonOperand) : SurfaceComputationPredicate :=
  .tokenComparison .equal left right

example : run .string false (firstToken (.firstFilled { first := .field (path "A"), rest := [.field (path "B")] }) (.literal "a"))
      (context .string (.parsed (.str "a")) (.rejected .malformed)) = some .holds ∧
    run .string false (firstToken (.firstFilled { first := .field (path "A"), rest := [.field (path "B")] }) (.literal ""))
      (context .string (.rejected .malformed) (.parsed (.str "a"))) = some (.poison .malformed) ∧
    run .string false (firstToken (.firstFilled { first := .field (path "A"), rest := [.field (path "B")] }) (.field (path "B")))
      (context .string (.parsed (.str "a")) (.rejected .malformed)) = some (.poison .malformed) := by native_decide

example : run .string true (firstToken (.firstFilled (star "A")) (.literal "other"))
      (starredContext .string true) = some .holds ∧
    run .string true (firstToken (.firstFilled (star "A")) (.firstFilled (star "B")))
      (starredContext .string true) = some .notTrue := by native_decide

end A12Kernel.Conformance.ComputationPredicate
