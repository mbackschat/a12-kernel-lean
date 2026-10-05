import A12Kernel.Elaboration.FieldFillList

/-! # Field-fill list conformance

A field-fill list concatenates its operands' observations, so the count and the quantifiers read one
stream while keeping their own rules for an invalid cell, and a starred field contributes its declared
slots to the declared-range quantifiers. The fixture is the model of the
[negation pair grid](../../evidence/kernel-30.8.1/captures/negation-pair-grid-2026-10-02/request.json):
three direct Number fields, a fixed group `G` of two Number fields, and one Number field in a `max 2`
repeatable group.
-/

namespace A12Kernel

private def listModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe"], name := "A", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 2, groupPath := ["Probe"], name := "B", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, groupPath := ["Probe"], name := "C", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 4, groupPath := ["Probe", "Rows"], name := "R",
        policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [4] },
      { id := 5, groupPath := ["Probe", "G"], name := "X", policy := { kind := .number { scale := 0, signed := true } } },
      { id := 6, groupPath := ["Probe", "G"], name := "Y", policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 4, path := ["Probe", "Rows"], repeatability := some 2 }] }

private def listPrepared : PreparedFlatStringContext listModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler listModel).toOption.get (by native_decide)

private def direct (name : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field := name }

private def directList : SurfaceFieldEntitySource :=
  { first := direct "A", rest := [direct "B", direct "C"] }

private def starredR : SurfaceFieldEntitySource :=
  { first := .star { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "R" },
    rest := [] }

private def cell (field : FieldId) (path : List Nat) (value : Int) : ClassifiedCellInput :=
  { address := { field, path }, stored := toString value, raw := .parsed (.num value) }

/-- A Number cell whose text no Number reading admits. -/
private def invalid (field : FieldId) (path : List Nat) : ClassifiedCellInput :=
  { address := { field, path }, stored := "x", raw := .rejected .malformed }

private def document? (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument listModel) :=
  (checkDocument listPrepared "en_US" { instantiatedRows := rows, cells }).toOption

private def fill (source : SurfaceFieldEntitySource) (operator : FieldFillQuantifier)
    (rows : List RowAddr) (cells : List ClassifiedCellInput) : Option ValidationFillOutcome := do
  let list ← (elaborateFieldFillList listModel ["Probe"] source ["Probe"] .quantifier).toOption
  (list.evaluateFill? operator (← document? rows cells) []).toOption.join

private def count (source : SurfaceFieldEntitySource) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let list ← (elaborateFieldFillList listModel ["Probe"] source).toOption
  (list.evaluateCountOperand? (← document? rows cells) []).toOption.join

/- One invalid cell beside one filled sibling: `AtLeastOneFieldFilled(A, B, C)` fires with VALUE while
the count over the same list is unavailable, so `NumberOfFilledFields(A, B, C) == 1` stays silent. A
count that skipped the invalid cell would read 1 and fire. The grid's `invalid-one-filled` row, which
also places `C` empty, fires the quantifier and leaves the count comparison silent. -/
example :
    fill directList .atLeastOneFieldFilled [] [invalid 1 [], cell 2 [] 7] = some (.fired .value) ∧
    count directList [] [invalid 1 [], cell 2 [] 7] = none := by
  native_decide

/- With no row instantiated, the starred field's two declared slots are the missing tail, so
`NotAllFieldsFilled(Rows*/R)` fires with OMISSION and `AllFieldsFilled(Rows*/R)` does not, as on the
grid's `rows-none-a` row. Reading only instantiated rows would make the list empty and vacuously
all-filled. -/
example :
    fill starredR .notAllFieldsFilled [] [] = some (.fired .omission) ∧
    fill starredR .allFieldsFilled [] [] = some .falseOrUnknown := by
  native_decide

private def groupG : SurfaceFieldEntityOperand := .group (.path { base := .relative 0, groups := ["G"] })

private def starR : SurfaceFieldEntityOperand :=
  .star { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "R" }

/- Mixed lists read each operand by its own source, as the
[mixed-list grid](../../evidence/kernel-30.8.1/captures/field-fill-mixed-list-2026-10-02/request.json)
observes: `AtLeastOneFieldFilled(A, G)` fires VALUE on an invalid `A` beside a filled `G/X`;
`NotAllFieldsFilled(A, Rows*/R, G)` fires OMISSION on a blank document, where the starred field's
declared slots are the tail; and `NoFieldFilled(B, Rows*/R)` is silent once `B` holds a value. -/
example :
    fill { first := direct "A", rest := [groupG] } .atLeastOneFieldFilled []
        [invalid 1 [], cell 5 [] 1, invalid 6 []] = some (.fired .value) ∧
    fill { first := direct "A", rest := [starR, groupG] } .notAllFieldsFilled [] [] =
        some (.fired .omission) ∧
    fill { first := direct "B", rest := [starR] } .noFieldFilled [] [cell 2 [] 7] =
        some .falseOrUnknown := by
  native_decide

private def filterFirst (op : SurfaceComparisonOp) (n : Int) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.repetition { origin := .inner, group := .path { base := .relative 0, groups := ["Rows"] } }))
    (.literal { value := (n : Rat), authoredScale := 0 })

private def filteredR (having : SurfaceCorrelatedHaving) : SurfaceFieldEntityOperand :=
  .starHaving { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "R" } having

private def selectedFirst : SurfaceFieldEntityOperand := filteredR (filterFirst .equal 1)

example : fill { first := selectedFirst, rest := [] } .allFieldsFilled
    [{ group := 4, path := [1] }] [cell 4 [1] 1] = some (.fired .omission) ∧
    fill { first := filteredR (filterFirst .greater 0), rest := [] } .allFieldsFilled
    [{ group := 4, path := [1] }] [cell 4 [1] 1] = some .falseOrUnknown := by native_decide

example : fill { first := direct "A", rest := [selectedFirst] } .atLeastOneFieldFilled
    [{ group := 4, path := [1] }] [cell 1 [] 7, cell 4 [1] 1] = some (.fired .value) ∧
    fill { first := selectedFirst, rest := [direct "A"] } .atLeastOneFieldFilled
    [{ group := 4, path := [1] }] [cell 1 [] 7, cell 4 [1] 1] = some (.fired .omission) := by native_decide

private def positiveR : SurfaceFieldEntityOperand := filteredR
  (.compareNumberLiteral .greater
    { origin := .inner, field := { base := .relative 0, groups := ["Rows"], field := "R" } }
    { value := 0, authoredScale := 0 })

example : fill { first := selectedFirst, rest := [] } .notAllFieldsFilled [] [] =
      some (.fired .omission) ∧
    fill { first := positiveR, rest := [] } .allFieldsFilled [] [] =
      some (.fired .omission) ∧
    fill { first := selectedFirst, rest := [] } .noFieldFilled
      [{ group := 4, path := [1] }] [invalid 4 [1]] = some .falseOrUnknown ∧
    fill { first := positiveR, rest := [] } .noFieldFilled
      [{ group := 4, path := [1] }] [invalid 4 [1]] = some (.fired .omission) := by native_decide

example : (do
    let document ← document? [] []
    pure ((document.read { field := 4, path := [1] }).toOption.isNone,
      (document.readDeclared { field := 4, path := [1] }).toOption.map (observeCell .validation),
      (document.readDeclared { field := 4, path := [0] }).toOption.isNone,
      (document.readDeclared { field := 4, path := [] }).toOption.isNone,
      (document.readDeclared { field := 99, path := [] }).toOption.isNone)) =
    some (true, some .empty, true, true, true) := by native_decide

example : (elaborateFieldFillList listModel ["Probe"]
      { first := selectedFirst, rest := [] }).isOk = true ∧
    (elaborateComputationFieldFillList listModel ["Probe"] ["Probe"]
      { first := selectedFirst, rest := [] }).isOk = true ∧
    (do
      let source ← (elaborateFieldFillList listModel ["Probe"]
        { first := selectedFirst, rest := [] } ["Probe"] .quantifier).toOption
      pure source.computationSources.toOption.isNone) = some true := by native_decide

example : (do
    let model := { listModel with repeatableGroups :=
      [{ level := 4, path := ["Probe", "Rows"], repeatability := none }] }
    let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
    let document ← (checkDocument prepared "en_US"
      { instantiatedRows := [{ group := 4, path := [1] }], cells := [cell 4 [1] 1] }).toOption
    let source ← (elaborateFieldFillList model ["Probe"]
      { first := selectedFirst, rest := [] } ["Probe"] .quantifier).toOption
    pure ((source.evaluateFill? .atLeastOneFieldFilled document []).toOption.join,
      (source.evaluateFill? .allFieldsFilled document []).toOption.join)) =
    some (some (.fired .omission), none) := by native_decide

example : (do
    let model : FlatModel := {
      fields := [{
        id := 4
        groupPath := ["Probe", "Rows", "Inner"]
        name := "R"
        repeatableScope := [4, 5]
        policy := { kind := .number { scale := 0, signed := true } } }]
      repeatableGroups := [
        { level := 4, path := ["Probe", "Rows"], repeatability := some 2 },
        { level := 5, path := ["Probe", "Rows", "Inner"], repeatability := some 2 }] }
    let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
    let document ← (checkDocument prepared "en_US"
      { instantiatedRows := [{ group := 4, path := [1] }], cells := [] }).toOption
    let source ← (elaborateStarFieldPath model ["Probe", "Rows"]
      { base := .relative 0, groups := [{ name := "Inner", starred := true }], field := "R" }).toOption
    pure ((source.declaredEnvironments? document [(4, 1)]).toOption.join,
      (source.declaredEnvironments? document [(4, 2)]).toOption.isNone)) =
    some (some [[(4, 1), (5, 1)], [(4, 1), (5, 2)]], true) := by native_decide

private def filteredCountSource : SurfaceFieldEntitySource := {
  first := direct "A"
  rest := [.starHaving
    { base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "R" }
    (.presence .filled { origin := .inner, field := { base := .relative 0, groups := ["Rows"], field := "R" } })] }

example : count filteredCountSource [{ group := 4, path := [1] }, { group := 4, path := [2] }]
    [cell 1 [] 1, cell 4 [1] 2, invalid 4 [2]] = some (.value 2 .both) := by native_decide

example : count filteredCountSource [{ group := 4, path := [1] }, { group := 4, path := [2] }, { group := 4, path := [3] }]
    [cell 4 [1] 2, cell 4 [3] 3] = some (.value 1 .both) := by native_decide

example : count filteredCountSource [] [] = some (.value 0 .growOnly) ∧
    count filteredCountSource [] [cell 1 [] 1] = some (.value 1 .growOnly) ∧
    count filteredCountSource [] [invalid 1 []] = none := by native_decide

example : count { first := direct "A", rest := [selectedFirst] }
    [{ group := 4, path := [1] }] [cell 1 [] 1] = some (.value 1 .growOnly) ∧
    count { first := selectedFirst, rest := [direct "A"] }
    [{ group := 4, path := [1] }] [cell 1 [] 1] = some (.value 1 .growOnly) := by native_decide

private def indexedListModel : FlatModel := {
  listModel with
  fields := (listModel.fields.map fun declaration =>
    if declaration.id == 4 then { declaration with policy := { kind := .number { scale := 1, signed := true } } }
    else declaration) ++ [{
    id := 7, groupPath := ["Probe", "Rows"], name := "Value",
    policy := { kind := .string }, repeatableScope := [4] }]
  repeatableGroups := [{
    level := 4, path := ["Probe", "Rows"], repeatability := some 2, indexField := some 4 }] }

private def indexedValue (key : Rat) (spelling : String) : SurfaceFieldEntityOperand :=
  .indexed {
    target := { base := .absolute, groups := ["Probe", "Rows"], field := "Value" }
    key := .literal (.number key) (some spelling) }

private def indexListAdmitted (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) : Bool :=
  (elaborateFieldEntityShape indexedListModel ["Probe"] { first, rest }
    (writtenGroup := ["Probe"])).isOk

example : indexListAdmitted (indexedValue 1 "1") [direct "A"] = true := by native_decide
example : indexListAdmitted (indexedValue 1 "1") [] = false := by native_decide
example : indexListAdmitted (indexedValue 1 "1") [indexedValue 1 "1"] = false := by native_decide
example : indexListAdmitted (indexedValue 1 "1") [indexedValue 2 "2"] = true := by native_decide
example : indexListAdmitted (indexedValue 1 "1") [indexedValue 1 "1.0"] = true := by native_decide
example : indexListAdmitted (indexedValue 1 "1")
    [.starredGroup { base := .absolute, groups := [⟨"Probe", false⟩, ⟨"Rows", true⟩] }] = true := by native_decide

private def indexedListData (secondKey : Rat := 2) (badTarget : Bool := false) : DocumentData := {
  instantiatedRows := [1, 2, 3].map fun row => { group := 4, path := [row] }
  cells := [
    { address := { field := 4, path := [1] }, stored := "1", raw := .parsed (.num 1) },
    { address := { field := 4, path := [2] }, stored := toString secondKey,
      raw := .parsed (.num secondKey) },
    { address := { field := 4, path := [3] }, stored := "3", raw := .parsed (.num 3) },
    { address := { field := 7, path := [1] }, stored := "filled",
      raw := if badTarget then .rejected .malformed else .parsed (.str "filled") },
    { address := { field := 7, path := [3] }, stored := "overflow", raw := .parsed (.str "overflow") }] }

private def indexedValidationCount (key : Rat) (secondKey : Rat := 2) (badTarget : Bool := false) :
    Option (Option NumericOperand) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler indexedListModel).toOption
  let document ← (checkDocument prepared "en_US" (indexedListData secondKey badTarget)).toOption
  let source ← (elaborateFieldFillList indexedListModel ["Probe"] {
    first := indexedValue key (toString key), rest := [direct "A"] }).toOption
  (source.evaluateCountOperand? document []).toOption

example : indexedValidationCount 1 = some (some (.value 1 .growOnly)) := by native_decide
example : indexedValidationCount 2 = some (some (.value 0 .growOnly)) := by native_decide
example : indexedValidationCount 3 = some (some (.value 0 .growOnly)) := by native_decide
example : indexedValidationCount 1 1 = some none := by native_decide
example : indexedValidationCount 1 2 true = some none := by native_decide

private def partialListCount (source : SurfaceFieldEntitySource)
    (scope : ValidationRelevanceScope) (missing : Option FieldId := none)
    (invalidated : Option FieldId := none) :
    Option (Option PartialValidationFilledFieldCountResult) := do
  let checked ← (elaborateFieldFillList listModel ["Probe"] source).toOption
  let document ← document? [{ group := 4, path := [1] }]
    [cell 1 [] 1, cell 4 [1] 1, cell 5 [] 1, cell 6 [] 1]
  (checked.evaluatePartialCount document [] scope fun environment field => do
    if missing == some field then return none
    if invalidated == some field then return some { rawPresent := true, parsed := none, findings := [.malformed] }
    some <$> (document.fullValidationAddressedCell environment field).map (·.cell)).toOption

private def partialExtent (paths : List (List String)) : ValidationRelevanceScope :=
  .partialSet (paths.map fun path => { path, indices := path.map fun _ => .all })

example : partialListCount { first := direct "A", rest := [starR, groupG] } .full =
    some (some (.evaluated (.value 4))) ∧
    partialListCount { first := direct "A", rest := [starR, groupG] }
      (partialExtent [["Probe", "A"], ["Probe", "Rows", "R"], ["Probe", "G", "X"],
        ["Probe", "G", "Y"]]) = some (some (.evaluated (.value 4))) ∧
    partialListCount { first := direct "A", rest := [starR, groupG] }
      (partialExtent [["Probe", "A"], ["Probe", "Rows", "R"], ["Probe", "G", "X"]]) =
      some (some .nonRelevant) := by native_decide

example : partialListCount directList .full (some 1) = some (some .silentlyUnavailable) ∧
    partialListCount directList .full none (some 1) = some (some (.evaluated .unknown)) ∧
    partialListCount { first := starR, rest := [] } .full (some 4) =
      some (some .silentlyUnavailable) ∧
    partialListCount { first := groupG, rest := [] } .full none (some 6) =
      some (some (.evaluated .unknown)) := by native_decide

example : partialListCount { first := selectedFirst, rest := [] } .full =
    some (some .skippedHaving) := by native_decide

example : ((elaborateFieldFillList indexedListModel ["Probe"] {
    first := indexedValue 1 "1", rest := [direct "A"] }).toOption.map (·.supportsPartialCount)) =
    some false := by native_decide

end A12Kernel
