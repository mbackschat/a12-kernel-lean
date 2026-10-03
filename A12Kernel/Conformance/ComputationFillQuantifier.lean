import A12Kernel.Elaboration.FieldFillList

/-! # Computation field-fill quantifier locks

These examples exercise the seven resolved field-fill scans and the checked field-list computation projection. They distinguish instantiated empty cells from declared-but-uninstantiated slots, preserve per-declaration omission order and checked overlays, and lock the first reached poison. Filters and guard integration remain outside this module.
-/

namespace A12Kernel.Conformance.ComputationFillQuantifier

open A12Kernel

private def malformed : FormalCause := .malformed
private def constrained : FormalCause := .declaredConstraint

private def eval (operator : FieldFillQuantifier)
    (slots : List ComputationFillSlot) : ComputationConditionResult :=
  operator.evalComputation slots

/- Declared-range operators observe an uninstantiated slot as empty. -/
example : eval .allFieldsFilled [.uninstantiated] = .notTrue := by rfl
example : eval .notAllFieldsFilled [.uninstantiated] = .holds := by rfl

/- Instantiated-range operators ignore the same slot. -/
example : eval .noFieldFilled [.uninstantiated] = .holds := by rfl
example : eval .atLeastOneFieldFilled [.uninstantiated] = .notTrue := by rfl
example : eval .moreThanOneFieldFilled [.uninstantiated] = .notTrue := by rfl
example : eval .moreThanOneFieldFilled [.filled, .empty] = .notTrue := by rfl
example : eval .notExactlyOneFieldFilled [.uninstantiated] = .holds := by rfl
example : eval .fieldsNotCollectivelyFilled [.uninstantiated] = .notTrue := by rfl

/- Every operator ignores poison after its own deciding prefix. -/
example : eval .allFieldsFilled [.empty, .poison malformed] = .notTrue := by rfl
example : eval .notAllFieldsFilled [.empty, .poison malformed] = .holds := by rfl
example : eval .noFieldFilled [.filled, .poison malformed] = .notTrue := by rfl
example : eval .atLeastOneFieldFilled [.filled, .poison malformed] = .holds := by rfl
example : eval .moreThanOneFieldFilled [.filled, .filled, .poison malformed] = .holds := by rfl
example : eval .notExactlyOneFieldFilled [.filled, .filled, .poison malformed] = .holds := by rfl
example : eval .fieldsNotCollectivelyFilled [.empty, .filled, .poison malformed] = .holds := by rfl

/- A poison reached before the decision keeps its exact cause. -/
example : eval .allFieldsFilled [.filled, .poison malformed, .empty] =
    .poison malformed := by rfl
example : eval .noFieldFilled [.empty, .poison constrained, .filled] =
    .poison constrained := by rfl
example : eval .moreThanOneFieldFilled [.filled, .poison malformed, .filled] =
    .poison malformed := by rfl
example : eval .notExactlyOneFieldFilled [.filled, .poison constrained, .filled] =
    .poison constrained := by rfl
example : eval .fieldsNotCollectivelyFilled [.filled, .poison malformed, .empty] =
    .poison malformed := by rfl

/- The mixed operator uses instantiated presence and declared absence. -/
example : eval .fieldsNotCollectivelyFilled [.uninstantiated, .filled, .poison malformed] =
    .holds := by rfl
example : eval .fieldsNotCollectivelyFilled [.filled, .poison malformed, .uninstantiated] =
    .poison malformed := by rfl

/- Zero, exactly one, and at least two filled slots remain distinct. -/
example : eval .notExactlyOneFieldFilled [.empty, .uninstantiated] = .holds := by rfl
example : eval .notExactlyOneFieldFilled [.empty, .filled, .uninstantiated] = .notTrue := by rfl
example : eval .notExactlyOneFieldFilled [.filled, .empty, .filled] = .holds := by rfl

private def number (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath := groups, name, policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := scope }

private def groupModel (invalidFirst : Bool) : FlatModel :=
  let nested := number 1 ["Form", "Inputs", "Entries"] "First" [10]
  let later := number 2 ["Form", "Inputs"] "Later"
  { fields := if invalidFirst then [later, nested] else [nested, later]
    repeatableGroups := [{
      level := 10, path := ["Form", "Inputs", "Entries"], repeatability := some 3 }] }

private def groupSource : SurfaceFieldEntitySource :=
  { first := .group (.path { base := .absolute, groups := ["Form", "Inputs"] }), rest := [] }

private def numberCell (id : FieldId) (path : List Nat) (text : String) : ClassifiedCellInput :=
  { address := { field := id, path }, stored := text
    raw := match text.toInt? with
      | some value => .parsed (.num value)
      | none => .rejected .malformed }

private def slots (model : FlatModel) (source : SurfaceFieldEntitySource)
    (data : DocumentData) (outer : Env := []) (hidden : List FieldId := [])
    (placements : List CheckedCellPlacement := [])
    (targetGroup : GroupPath := ["Form"]) : Option (List ComputationFillSlot) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let list ← (elaborateComputationFieldFillList model ["Form"] targetGroup source).toOption
  (list.computationSlots (checked.overlayCells hidden placements) outer).toOption

private def operators : List FieldFillQuantifier :=
  [.allFieldsFilled, .noFieldFilled, .atLeastOneFieldFilled, .moreThanOneFieldFilled,
    .notAllFieldsFilled, .notExactlyOneFieldFilled, .fieldsNotCollectivelyFilled]

private def signature (slots : List ComputationFillSlot) : String :=
  String.ofList (operators.map fun operator => match operator.evalComputation slots with
    | .holds => 'T' | .notTrue => 'F' | .poison _ => 'P')

private def groupSlots (invalidFirst : Bool) (rows : Nat)
    (filledRows : List Nat) (later : Option String) : Option (List ComputationFillSlot) :=
  slots (groupModel invalidFirst) groupSource {
    instantiatedRows := (List.range rows).map fun n => { group := 10, path := [n + 1] }
    cells := (filledRows.map fun n => numberCell 1 [n] "1") ++
      later.toList.map (numberCell 2 []) }

/- The retained field-fill guard grid requires a declared omission before the next declaration,
so the invalid tail is unread by the declared-range scan that already found its empty witness. -/
example :
    groupSlots false 1 [1] (some "bad") =
      some [.filled, .uninstantiated, .poison .malformed] ∧
    groupSlots true 1 [1] (some "bad") =
      some [.poison .malformed, .filled, .uninstantiated] := by
  native_decide

example :
    ([0, 1, 2, 3].map fun n =>
      (groupSlots false n ((List.range n).map (· + 1)) (some "bad")).map signature) =
        [some "FPPPTPP", some "FFTPTPT", some "FFTTTTT", some "PFTTPTP"] ∧
    ([0, 1, 2, 3].map fun n =>
      (groupSlots true n ((List.range n).map (· + 1)) (some "bad")).map signature) =
        List.replicate 4 (some "PPPPPPP") ∧
    (groupSlots false 4 [4] none).map signature = some "FTFFTTF" ∧
    (groupSlots false 1 [] (some "1")).map signature = some "FFTFTFT" := by
  native_decide

private def directModel : FlatModel :=
  { fields := [number 1 ["Form"] "A", number 2 ["Form"] "B", number 3 ["Form"] "C"] }

private def directSource : SurfaceFieldEntitySource :=
  { first := .field { base := .absolute, groups := ["Form"], field := "A" }
    rest := [.field { base := .absolute, groups := ["Form"], field := "B" },
      .field { base := .absolute, groups := ["Form"], field := "C" }] }

private def directSignature (values : List (Option String)) : Option String :=
  (slots directModel directSource {
    instantiatedRows := []
    cells := values.zipIdx |>.filterMap fun (value, i) => value.map (numberCell (i + 1) []) }).map signature

example :
    [directSignature [none, none, none], directSignature [some "1", some "2", some "3"],
      directSignature [none, some "1", none], directSignature [some "1", some "2", none],
      directSignature [some "bad", some "1", none], directSignature [none, some "1", some "bad"],
      directSignature [some "1", some "bad", none], directSignature [some "1", some "2", some "bad"],
      directSignature [none, some "bad", some "1"]] =
      [some "FTFFTTF", some "TFTTFTF", some "FFTFTFT", some "FFTTTTT", some "PPPPPPP",
        some "FFTPTPT", some "PFTPPPP", some "PFTTPTP", some "FPPPTPP"] := by
  native_decide

private def starSource : SurfaceFieldEntitySource :=
  { first := .star {
      base := .absolute
      groups := [{ name := "Form" }, { name := "Inputs" }, { name := "Entries", starred := true }]
      field := "First" }, rest := [] }

example :
    slots (groupModel false) starSource { instantiatedRows := [], cells := [] } =
      some [.uninstantiated] ∧
    slots (groupModel false) starSource {
      instantiatedRows := [{ group := 10, path := [1] }], cells := [numberCell 1 [1] "1"] } =
      some [.filled, .uninstantiated] := by
  native_decide

example :
    let data : DocumentData := {
      instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
      cells := [numberCell 1 [1] "1", numberCell 1 [2] "bad"] }
    slots (groupModel false) groupSource data =
      some [.filled, .poison .malformed, .uninstantiated, .empty] ∧
    slots (groupModel false) starSource data =
      some [.filled, .poison .malformed, .uninstantiated] := by
  native_decide

example :
    slots directModel directSource { instantiatedRows := [], cells := [] } [] []
      [{ address := { field := 1, path := [] }
         cell := { rawPresent := false, parsed := none, findings := [.required] } }] =
        some [.empty, .empty, .empty] := by
  native_decide

/- Slot values come from the checked overlay; source topology supplies addresses only. -/
example :
    slots (groupModel false) groupSource {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [numberCell 1 [1] "bad", numberCell 2 [] "bad"] } [] [1, 2]
      [{ address := { field := 1, path := [1] }
         cell := { rawPresent := true, parsed := some (.num 1), findings := [] } }] =
        some [.filled, .uninstantiated, .empty] := by
  native_decide

private def boundSource : SurfaceFieldEntitySource :=
  { first := .field { base := .absolute, groups := ["Form", "Inputs", "Entries"], field := "First" }
    rest := [.field { base := .absolute, groups := ["Form", "Inputs"], field := "Later" }] }

example :
    ((elaborateComputationFieldFillList (groupModel false) ["Form"]
      ["Form", "Inputs", "Entries"] boundSource).toOption.map fun list =>
        (list.declarations.map (·.id), list.bindingScope)) = some ([1, 2], [10]) := by
  native_decide

example :
    (match elaborateComputationFieldFillList (groupModel false)
      ["Form", "Inputs", "Entries"] ["Form"] boundSource with
    | .error (.shape (.unboundOperandLevel _)) => true
    | _ => false) = true := by
  native_decide

example :
    slots (groupModel false) boundSource {
      instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
      cells := [numberCell 1 [1] "bad", numberCell 1 [2] "1"] }
      [(10, 2)] [] [] ["Form", "Inputs", "Entries"] = some [.filled, .empty] ∧
    (elaborateFieldFillList (groupModel false) ["Form"] boundSource).isOk = false := by
  native_decide

private def admissionRefusals : Bool :=
  let single := elaborateComputationFieldFillList directModel ["Form"] ["Form"]
    { directSource with rest := [] }
  let duplicate := elaborateComputationFieldFillList directModel ["Form"] ["Form"]
    { directSource with rest := [directSource.first] }
  let overlap := elaborateComputationFieldFillList (groupModel false) ["Form"] ["Form"]
    { groupSource with rest := boundSource.rest }
  let root := elaborateComputationFieldFillList directModel ["Form"] ["Form"]
    { first := .group (.path { base := .absolute, groups := ["Form"] }), rest := [] }
  (match single with | .error (.shape .tooFewFields) => true | _ => false) &&
  (match duplicate with | .error (.shape (.duplicateOperand 1)) => true | _ => false) &&
  (match overlap with
    | .error (.shape (.overlappingOperands ["Form", "Inputs"] ["Form", "Inputs", "Later"])) => true
    | _ => false) &&
  (match root with | .error (.shape (.rootGroupOperand ["Form"])) => true | _ => false)

example : admissionRefusals = true := by native_decide

example :
    let source : SurfaceFieldEntitySource := {
      first := .starredGroup {
        base := .absolute
        groups := [{ name := "Form" }, { name := "Inputs" }, { name := "Entries", starred := true }] }
      rest := [] }
    slots (groupModel false) source {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [numberCell 1 [1] "1"] } = some [.filled, .uninstantiated] := by
  native_decide

private def detailModel : FlatModel :=
  { groupModel false with
    fields := [number 1 ["Form", "Inputs", "Entries", "Detail"] "First" [10]] }

example :
    let source : SurfaceFieldEntitySource := {
      first := .starredGroup {
        base := .absolute
        groups := [{ name := "Form" }, { name := "Inputs" },
          { name := "Entries", starred := true }, { name := "Detail" }] }
      rest := [] }
    slots detailModel source {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [numberCell 1 [1] "1"] } = some [.filled, .uninstantiated] := by
  native_decide

end A12Kernel.Conformance.ComputationFillQuantifier
