import A12Kernel.Elaboration.CurrentRepetitionStringToNumberRelation
import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # CurrentRepetition String-to-Number cascade locks -/

namespace A12Kernel.Conformance.CurrentRepetitionStringToNumber

open A12Kernel

private def base : FlatFieldDecl := {
  id := 1
  groupPath := ["Shipment", "Lines"]
  name := "BaseNumber"
  policy := { kind := .number { scale := 0, signed := true } }
  repeatableScope := [10]
}

private def first : FlatFieldDecl := {
  id := 2
  groupPath := ["Shipment", "Lines"]
  name := "FirstString"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }
  stringPatternSource := some asciiDigitsPatternSource
  repeatableScope := [10]
}

private def second : FlatFieldDecl := {
  id := 3
  groupPath := ["Shipment", "Lines"]
  name := "SecondNumber"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [10]
}

private def otherString : FlatFieldDecl := {
  first with id := 4, name := "OtherString"
}

private def lines : RepeatableGroupDecl := {
  level := 10
  path := ["Shipment", "Lines"]
  repeatability := some 10
}

private def other : RepeatableGroupDecl := {
  level := 20
  path := ["Shipment", "Other"]
  repeatability := some 10
}

private def model : FlatModel := {
  fields := [base, first, second, otherString]
  repeatableGroups := [lines, other]
}

private def bare (field : String) : SurfaceFieldPath := {
  base := .relative 0
  groups := []
  field
}

private def group : SurfaceGroupPath := {
  base := .absolute
  groups := ["Shipment", "Lines"]
}

private def otherGroup : SurfaceGroupPath := {
  base := .absolute
  groups := ["Shipment", "Other"]
}

private def plan? :
    Option (CheckedCurrentRepetitionStringToNumberCascade model) :=
  (checkCurrentRepetitionStringToNumberCascade model lines.path group
    first.id (bare "BaseNumber") second.id (.direct (bare "FirstString"))).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def numericCell (field : FieldId) (row : Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path := [row] }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def stringCell (row : Nat) (value : String) :
    ClassifiedCellInput := {
  address := { field := first.id, path := [row] }
  stored := value
  raw := .parsed (.str value)
}

private def otherStringCell (row : Nat) (value : String) :
    ClassifiedCellInput := {
  address := { field := otherString.id, path := [row] }
  stored := value
  raw := .parsed (.str value)
}

private def checkedInput? (rows : List Nat)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.map fun row =>
      { group := lines.level, path := [row] }
    cells
  }).toOption

private def twoRowInput? (firstBase : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  checkedInput? [1, 2] [
    firstBase,
    stringCell 1 "70",
    numericCell second.id 1 700,
    numericCell base.id 2 11,
    stringCell 2 "110",
    numericCell second.id 2 1100]

private def rowOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List
      (Nat × CellAddr × StringTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.string.targetField, row.string.outcome,
      row.number.targetField, row.number.outcome))

private def phasedOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List Nat × List (CellAddr × StringTargetOutcome) ×
      List (CellAddr × NumericTargetOutcome)) := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let string <- plan.executeStringPhase prepared.patterns input |>.toOption
  let number <- plan.executeNumberPhase input string |>.toOption
  pure (string.coordinates,
    string.outcomes.map fun outcome =>
      (outcome.targetField, outcome.outcome),
    number.map fun outcome => (outcome.targetField, outcome.outcome))

private def resultView? (input : CheckedDocument model) :
    Option (StringToNumberComputationRunView Unit Unit CellAddr) := do
  let plan ← plan?
  plan.executeResult prepared.patterns input (fun _ => ()) []
    ([] : List Unit) |>.toOption

private def twoRowInputWithTargets? (firstBase : ClassifiedCellInput)
    (firstString : String) (firstNumber : Int)
    (secondString : String) (secondNumber : Int) :
    Option (CheckedDocument model) :=
  checkedInput? [1, 2] [
    firstBase,
    stringCell 1 firstString,
    numericCell second.id 1 firstNumber,
    otherStringCell 1 "KEEP",
    numericCell base.id 2 11,
    stringCell 2 secondString,
    numericCell second.id 2 secondNumber]

private structure ResultApplicationSummary where
  stringChanges : List (CellAddr × String)
  numberChanges : List (CellAddr × StoredNumber)
  baseAtFirst : NumericTargetState
  stringAtFirst : StringTargetState
  stringAtSecond : StringTargetState
  otherStringAtFirst : StringTargetState
  numberAtFirst : NumericTargetState
  numberAtSecond : NumericTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? (input destination : CheckedDocument model) :
    Option ResultApplicationSummary := do
  let view ← resultView? input
  let stringApplied ←
    view.string.applyToCheckedOneLevel destination lines.level |>.toOption
  let numberApplied ← view.number.applyToChecked destination |>.toOption
  pure {
    stringChanges := view.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    numberChanges := view.number.withChanges.map fun item =>
      (item.targetField, item.value)
    baseAtFirst := numberApplied.stateAt { field := base.id, path := [1] }
    stringAtFirst := stringApplied.stateAt { field := first.id, path := [1] }
    stringAtSecond := stringApplied.stateAt { field := first.id, path := [2] }
    otherStringAtFirst :=
      stringApplied.stateAt { field := otherString.id, path := [1] }
    numberAtFirst := numberApplied.stateAt { field := second.id, path := [1] }
    numberAtSecond := numberApplied.stateAt { field := second.id, path := [2] }
  }

private structure FailureApplicationSummary where
  stringErrors : List (CellAddr × StringTargetError)
  stringCleared : List CellAddr
  numberCleared : List CellAddr
  stringAtFirst : StringTargetState
  stringAtSecond : StringTargetState
  numberAtFirst : NumericTargetState
  numberAtSecond : NumericTargetState
  deriving Repr, DecidableEq

private def failureApplicationSummary? (input : CheckedDocument model) :
    Option FailureApplicationSummary := do
  let view ← resultView? input
  let stringApplied ←
    view.string.applyToCheckedOneLevel input lines.level |>.toOption
  let numberApplied ← view.number.applyToChecked input |>.toOption
  pure {
    stringErrors := view.string.withErrors.map fun item =>
      (item.targetField, item.cause)
    stringCleared := view.string.cleared
    numberCleared := view.number.cleared
    stringAtFirst := stringApplied.stateAt { field := first.id, path := [1] }
    stringAtSecond := stringApplied.stateAt { field := first.id, path := [2] }
    numberAtFirst := numberApplied.stateAt { field := second.id, path := [1] }
    numberAtSecond := numberApplied.stateAt { field := second.id, path := [2] }
  }

private def encounterOrderOutcomes? :
    Option (List
      (Nat × CellAddr × StringTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan <- plan?
  let input <- checkedInput? [3, 1, 2] [
    numericCell base.id 1 7,
    stringCell 1 "70",
    numericCell second.id 1 700,
    numericCell base.id 2 11,
    stringCell 2 "110",
    numericCell second.id 2 1100,
    numericCell base.id 3 13,
    stringCell 3 "130",
    numericCell second.id 3 1300]
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.string.targetField, row.string.outcome,
      row.number.targetField, row.number.outcome))

private def storedString (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

/- Analyze keeps the structural coordinate separate from the two cross-family field edges. -/
example :
    plan?.map CheckedCurrentRepetitionStringToNumberCascade.analyze = some {
      structuralGroup := lines.path
      scope := [lines.level]
      fieldDependencies := [
        (first.id, [base.id]),
        (second.id, [first.id])]
    } := by
  native_decide

/- Distinct seeded rows consume each newly computed String only at its own Number address. -/
example :
    rowOutcomes? (numericCell base.id 1 7) = some [
      (1, { field := first.id, path := [1] },
        .accepted (storedString "7" (by decide)),
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- The explicit phase boundary retains every fresh String completion before the dependent Number phase reads it, rather than re-reading stale seeded targets. -/
example :
    phasedOutcomes? (numericCell base.id 1 7) = some (
      [1, 2],
      [({ field := first.id, path := [1] },
          .accepted (storedString "7" (by decide))),
        ({ field := first.id, path := [2] },
          .accepted (storedString "11" (by decide)))],
      [({ field := second.id, path := [1] },
          .accepted { unscaled := 7, scale := 0 }),
        ({ field := second.id, path := [2] },
          .accepted { unscaled := 11, scale := 0 })]) := by
  native_decide

/- A wider finite input preserves physical encounter order rather than sorting by coordinate. -/
example :
    encounterOrderOutcomes? = some [
      (3, { field := first.id, path := [3] },
        .accepted (storedString "13" (by decide)),
        { field := second.id, path := [3] },
        .accepted { unscaled := 13, scale := 0 }),
      (1, { field := first.id, path := [1] },
        .accepted (storedString "7" (by decide)),
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Number empty produces String no-value, then the reached conversion supplies Number zero only in that row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := ""
      raw := .presentEmpty
    } = some [
      (1, { field := first.id, path := [1] }, .noValue,
        { field := second.id, path := [1] },
        .accepted { unscaled := 0, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Reached String poison becomes cause-blind Number dependency poison without aborting another row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    } = some [
      (1, { field := first.id, path := [1] }, .poison .malformed,
        { field := second.id, path := [1] },
        .inheritedPoison .computedDependency),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

private def selectedLines : RepeatableGroupDecl := {
  lines with repeatability := some 2, indexField := some base.id
}

private def selectedModel : FlatModel := {
  fields := [base, first, second, otherString]
  repeatableGroups := [selectedLines, other]
}

private def selectedPrepared :
    PreparedFlatStringContext selectedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler selectedModel).toOption.get (by native_decide)

private def selectedPlan? :
    Option (CheckedCurrentRepetitionStringToNumberCascade selectedModel) :=
  (checkCurrentRepetitionStringToNumberCascade selectedModel selectedLines.path
    group first.id (bare base.name) second.id
    (.direct (bare first.name))).toOption

private def selectedInput? : Option (CheckedDocument selectedModel) :=
  (checkDocument selectedPrepared "en_US" {
    instantiatedRows := [
      { group := selectedLines.level, path := [1] },
      { group := selectedLines.level, path := [2] }]
    cells := [
      numericCell base.id 1 7, numericCell base.id 2 7,
      stringCell 1 "70", stringCell 2 "70",
      numericCell second.id 1 700, numericCell second.id 2 700]
  }).toOption

private structure SelectedCascadeSummary where
  selectedFields : List FieldId
  formalErrors : List ComputationFormalInputFinding
  stringCleared : List CellAddr
  numberCleared : List CellAddr
  stringErrors : List (CellAddr × StringTargetError)
  phaseResidualCounts : Nat × Nat
  deriving Repr, DecidableEq

private def selectedCascadeSummary? : Option SelectedCascadeSummary := do
  let plan ← selectedPlan?
  let input ← selectedInput?
  let inputPlan ← plan.formalInputPlan |>.toOption
  let view ← plan.executeResultWithFormalInputs selectedPrepared.patterns input
    |>.toOption
  pure {
    selectedFields := inputPlan.selectedFields
    formalErrors := view.formalErrorsInOperands
    stringCleared := view.phases.string.cleared
    numberCleared := view.phases.number.cleared
    stringErrors := view.phases.string.withErrors.map fun item =>
      (item.targetField, item.cause)
    phaseResidualCounts := (view.phases.string.formalErrorsInOperands.length,
      view.phases.number.formalErrorsInOperands.length)
  }

/- Duplicate selected Number indexes poison both reached String conversions, whose completed dependency cells become cause-blind poison for the Number phase; eager findings remain whole-call only. -/
example : selectedCascadeSummary? = some {
  selectedFields := [base.id]
  formalErrors := [
    { address := { field := base.id, path := [1] }, cause := .duplicateIndex },
    { address := { field := base.id, path := [2] }, cause := .duplicateIndex }]
  stringCleared := [
    { field := first.id, path := [1] },
    { field := first.id, path := [2] }]
  numberCleared := [
    { field := second.id, path := [1] },
    { field := second.id, path := [2] }]
  stringErrors := []
  phaseResidualCounts := (0, 0)
} := by
  native_decide

/- A producer target error retains its attempted String but becomes the same cause-blind Number dependency poison. -/
example :
    rowOutcomes? (numericCell base.id 1 (-5)) = some [
      (1, { field := first.id, path := [1] },
        .errored (storedString "-5" (by decide)) .pattern,
        { field := second.id, path := [1] },
        .inheritedPoison .computedDependency),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Both addressed families project their changed rows and apply independently through the established String and Number checked-document carriers. -/
example : (do
    let input ← twoRowInput? (numericCell base.id 1 7)
    let destination ← twoRowInputWithTargets?
      (numericCell base.id 1 99) "dest1" 700 "dest2" 1100
    resultApplicationSummary? input destination) = some {
      stringChanges := [
        ({ field := first.id, path := [1] }, "7"),
        ({ field := first.id, path := [2] }, "11")]
      numberChanges := [
        ({ field := second.id, path := [1] },
          { unscaled := 7, scale := 0 }),
        ({ field := second.id, path := [2] },
          { unscaled := 11, scale := 0 })]
      baseAtFirst :=
        .presentValue (.decimal { unscaled := 99, scale := 0 })
      stringAtFirst := .presentValue (storedString "7" (by decide))
      stringAtSecond := .presentValue (storedString "11" (by decide))
      otherStringAtFirst := .presentValue (storedString "KEEP" (by decide))
      numberAtFirst :=
        .presentValue (.decimal { unscaled := 7, scale := 0 })
      numberAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
    } := by
  native_decide

/- Both phase results classify against immutable pre-computation source state, so source-identical successes stay inert against a different destination. -/
example : (do
    let input ← twoRowInputWithTargets?
      (numericCell base.id 1 7) "7" 7 "11" 11
    let destination ← twoRowInputWithTargets?
      (numericCell base.id 1 99) "dest1" 700 "dest2" 1100
    resultApplicationSummary? input destination) = some {
      stringChanges := []
      numberChanges := []
      baseAtFirst :=
        .presentValue (.decimal { unscaled := 99, scale := 0 })
      stringAtFirst := .presentValue (storedString "dest1" (by decide))
      stringAtSecond := .presentValue (storedString "dest2" (by decide))
      otherStringAtFirst := .presentValue (storedString "KEEP" (by decide))
      numberAtFirst :=
        .presentValue (.decimal { unscaled := 700, scale := 0 })
      numberAtSecond :=
        .presentValue (.decimal { unscaled := 1100, scale := 0 })
    } := by
  native_decide

/- Reached producer poison clears both source-filled phase targets at row one while row-two successes remain changed and applicable. -/
example : (do
    let input ← twoRowInput? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    }
    failureApplicationSummary? input) = some {
      stringErrors := []
      stringCleared := [{ field := first.id, path := [1] }]
      numberCleared := [{ field := second.id, path := [1] }]
      stringAtFirst := .presentEmpty
      stringAtSecond := .presentValue (storedString "11" (by decide))
      numberAtFirst := .presentEmpty
      numberAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
    } := by
  native_decide

/- A producer target rejection remains a String ERRORED instance rather than CLEARED, while its dependent Number poison clears the source-filled Number target. Both established applications clear the existing row-one destination values. -/
example : (do
    let input ← twoRowInput? (numericCell base.id 1 (-5))
    failureApplicationSummary? input) = some {
      stringErrors := [({ field := first.id, path := [1] }, .pattern)]
      stringCleared := []
      numberCleared := [{ field := second.id, path := [1] }]
      stringAtFirst := .presentEmpty
      stringAtSecond := .presentValue (storedString "11" (by decide))
      numberAtFirst := .presentEmpty
      numberAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
    } := by
  native_decide

/- Wrong structural group, bypassed dependency, and reverse dependency fail before execution. -/
example :
    (match checkCurrentRepetitionStringToNumberCascade model lines.path otherGroup
        first.id (bare "BaseNumber") second.id (.direct (bare "FirstString")) with
      | .error (.groupMismatch source declaring) =>
          source == other.path && declaring == lines.path
      | _ => false) = true ∧
    (match checkCurrentRepetitionStringToNumberCascade model lines.path group
        first.id (bare "BaseNumber") second.id (.direct (bare "OtherString")) with
      | .error (.dependency expected actual) =>
          expected == first.id && actual == otherString.id
      | _ => false) = true ∧
    (match checkCurrentRepetitionStringToNumberCascade model lines.path group
        first.id (bare "SecondNumber") second.id (.direct (bare "FirstString")) with
      | .error (.reverseDependency field) => field == second.id
      | _ => false) = true := by
  native_decide

/- No physical target row remains explicit insufficient information. -/
example :
    (do
      let plan <- plan?
      let input <- checkedInput? [] []
      pure (match plan.execute prepared.patterns input with
        | .error (.rowCardinality 0) => true
        | _ => false)) = some true := by
  native_decide

private def transitionPlan :
    CheckedCurrentRepetitionStringToNumberCascade model :=
  plan?.get (by native_decide)

private def noRowsInput : CheckedDocument model :=
  (checkedInput? [] []).get (by native_decide)

private theorem noRowsStringPhaseFailed :
    transitionPlan.executeStringPhase prepared.patterns noRowsInput =
      .error (.rowCardinality 0) := by
  rfl

/- The concrete no-row fault terminates in the initial state before either
target family completes. -/
example :
    CurrentRepetitionStringToNumberFailureTransition transitionPlan
        prepared.patterns noRowsInput {} (.rowCardinality 0) ∧
      CurrentRepetitionStringToNumberFailureTrace transitionPlan
        prepared.patterns noRowsInput {} (.rowCardinality 0) := by
  have failed : CurrentRepetitionStringToNumberFailureTransition transitionPlan
      prepared.patterns noRowsInput {} (.rowCardinality 0) :=
    .string (.rowCardinality 0) noRowsStringPhaseFailed
  exact ⟨failed, .string failed⟩

private def transitionInput : CheckedDocument model :=
  (twoRowInput? (numericCell base.id 1 7)).get (by native_decide)

private def transitionStringPhase :
    CurrentRepetitionStringToNumberStringPhase :=
  (transitionPlan.executeStringPhase prepared.patterns transitionInput)
    |>.toOption |>.get (by native_decide)

private theorem evaluated_to_get (evaluation : Except ε α)
    (available : evaluation.toOption.isSome = true) :
    evaluation = .ok (evaluation.toOption.get available) := by
  cases evaluation with
  | error cause => simp [Except.toOption] at available
  | ok value => rfl

private theorem transitionStringExecuted :
    transitionPlan.executeStringPhase prepared.patterns transitionInput =
      .ok transitionStringPhase := by
  simpa [transitionStringPhase] using evaluated_to_get
    (evaluation := transitionPlan.executeStringPhase
      prepared.patterns transitionInput) (by native_decide)

/- A later structural Number fault is conditional for this fixture. If it
occurs, the trace retains the complete successful String phase and no Number
completion instead of resetting the cascade to its initial state. -/
example (fault : CurrentRepetitionStringToNumberFault)
    (numberFailed :
      transitionPlan.executeNumberPhase transitionInput transitionStringPhase =
        .error fault) :
    CurrentRepetitionStringToNumberFailureTrace transitionPlan
      prepared.patterns transitionInput
        { string := some transitionStringPhase } fault := by
  exact .number
    (.string transitionStringPhase transitionStringExecuted)
    (.number transitionStringPhase fault numberFailed)

private def nestedPath : GroupPath := ["Shipment", "Lines", "Entries"]

private def nestedBase : FlatFieldDecl := {
  base with groupPath := nestedPath, repeatableScope := [10, 20]
}

private def nestedFirst : FlatFieldDecl := {
  first with groupPath := nestedPath, repeatableScope := [10, 20]
}

private def nestedSecond : FlatFieldDecl := {
  second with groupPath := nestedPath, repeatableScope := [10, 20]
}

private def nestedModel : FlatModel := {
  fields := [nestedBase, nestedFirst, nestedSecond]
  repeatableGroups := [lines, {
    level := 20
    path := nestedPath
    repeatability := some 10
  }]
}

private def nestedGroup : SurfaceGroupPath := {
  base := .absolute
  groups := nestedPath
}

private def nestedPlan? :
    Option (CheckedCurrentRepetitionStringToNumberCascade nestedModel) :=
  (checkCurrentRepetitionStringToNumberCascade nestedModel nestedPath
    nestedGroup nestedFirst.id (bare "BaseNumber") nestedSecond.id
    (.direct (bare "FirstString"))).toOption

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedNumberCell (field : FieldId) (path : List Nat)
    (value : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def nestedStringCell (path : List Nat) : ClassifiedCellInput := {
  address := { field := nestedFirst.id, path }
  stored := "old"
  raw := .parsed (.str "old")
}

private def nestedOutcomes? : Option (List
    (Nat × CellAddr × StringTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan ← nestedPlan?
  let input ← (checkDocument nestedPrepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      nestedNumberCell nestedBase.id [1, 1] 7,
      nestedNumberCell nestedBase.id [2, 1] 11,
      nestedNumberCell nestedBase.id [1, 2] 13,
      nestedStringCell [1, 1], nestedStringCell [2, 1],
      nestedStringCell [1, 2],
      nestedNumberCell nestedSecond.id [1, 1] 700,
      nestedNumberCell nestedSecond.id [2, 1] 1100,
      nestedNumberCell nestedSecond.id [1, 2] 1300]
  }).toOption
  let outcomes ← plan.execute nestedPrepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.string.targetField, row.string.outcome,
      row.number.targetField, row.number.outcome))

/- A valid two-level model retains its complete scope and both typed field edges. -/
example :
    nestedPlan?.map CheckedCurrentRepetitionStringToNumberCascade.analyze = some {
          structuralGroup := nestedPath
          scope := [10, 20]
          fieldDependencies := [
            (nestedFirst.id, [nestedBase.id]),
            (nestedSecond.id, [nestedFirst.id])]
        } := by
  native_decide

/- Equal terminal coordinates under different parent rows retain distinct typed state at full addresses. -/
example : nestedOutcomes? = some [
    (1, { field := nestedFirst.id, path := [1, 1] },
      .accepted (storedString "7" (by decide)),
      { field := nestedSecond.id, path := [1, 1] },
      .accepted { unscaled := 7, scale := 0 }),
    (1, { field := nestedFirst.id, path := [2, 1] },
      .accepted (storedString "11" (by decide)),
      { field := nestedSecond.id, path := [2, 1] },
      .accepted { unscaled := 11, scale := 0 }),
    (2, { field := nestedFirst.id, path := [1, 2] },
      .accepted (storedString "13" (by decide)),
      { field := nestedSecond.id, path := [1, 2] },
      .accepted { unscaled := 13, scale := 0 })] := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionStringToNumber
