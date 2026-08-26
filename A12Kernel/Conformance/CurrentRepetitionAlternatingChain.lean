import A12Kernel.Elaboration.CurrentRepetitionAlternatingChainRelation
import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Elaboration.StringComputationRunApplication

/-! # CurrentRepetition alternating Number/String chain locks -/

namespace A12Kernel.Conformance.CurrentRepetitionAlternatingChain

open A12Kernel

private def base : FlatFieldDecl := {
  id := 1
  groupPath := ["Shipment", "Lines"]
  name := "BaseNumber"
  policy := { kind := .number { scale := 0, signed := true } }
  repeatableScope := [10]
}

private def first : FlatFieldDecl := {
  base with id := 2, name := "FirstNumber"
}

private def second : FlatFieldDecl := {
  id := 3
  groupPath := ["Shipment", "Lines"]
  name := "SecondString"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }
  stringPatternSource := some asciiDigitsPatternSource
  repeatableScope := [10]
}

private def third : FlatFieldDecl := {
  id := 4
  groupPath := ["Shipment", "Lines"]
  name := "ThirdNumber"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [10]
}

private def otherString : FlatFieldDecl := {
  second with id := 5, name := "OtherString"
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
  fields := [base, first, second, third, otherString]
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

private def plan? : Option (CheckedCurrentRepetitionAlternatingChain model) :=
  (checkCurrentRepetitionAlternatingChain model lines.path group
    first.id (bare "BaseNumber")
    second.id (bare "FirstNumber")
    third.id (.direct (bare "SecondString"))).toOption

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

private def stringCell (field : FieldId) (row : Nat) (value : String) :
    ClassifiedCellInput := {
  address := { field, path := [row] }
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
    numericCell first.id 1 70,
    stringCell second.id 1 "old1",
    numericCell third.id 1 700,
    numericCell base.id 2 11,
    numericCell first.id 2 110,
    stringCell second.id 2 "old2",
    numericCell third.id 2 1100]

private def resultView? (input : CheckedDocument model) :
    Option (StringNumberComputationRunView Unit Unit CellAddr) := do
  let plan ← plan?
  plan.executeResult prepared.patterns input (fun _ => ()) []
    ([] : List Unit) |>.toOption

private def twoRowInputWithTargets? (firstBase : ClassifiedCellInput)
    (firstFirst : Int) (firstSecond : String) (firstThird : Int)
    (secondFirst : Int) (secondSecond : String) (secondThird : Int) :
    Option (CheckedDocument model) :=
  checkedInput? [1, 2] [
    firstBase,
    numericCell first.id 1 firstFirst,
    stringCell second.id 1 firstSecond,
    numericCell third.id 1 firstThird,
    stringCell otherString.id 1 "KEEP",
    numericCell base.id 2 11,
    numericCell first.id 2 secondFirst,
    stringCell second.id 2 secondSecond,
    numericCell third.id 2 secondThird]

private structure ResultApplicationSummary where
  numberChanges : List (CellAddr × StoredNumber)
  stringChanges : List (CellAddr × String)
  numberCleared : List CellAddr
  stringCleared : List CellAddr
  stringErrors : List (CellAddr × StringTargetError)
  baseAtFirst : NumericTargetState
  firstAtFirst : NumericTargetState
  firstAtSecond : NumericTargetState
  secondAtFirst : StringTargetState
  secondAtSecond : StringTargetState
  thirdAtFirst : NumericTargetState
  thirdAtSecond : NumericTargetState
  otherStringAtFirst : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? (input destination : CheckedDocument model) :
    Option ResultApplicationSummary := do
  let view ← resultView? input
  let numberApplied ← view.number.applyToChecked destination |>.toOption
  let stringApplied ←
    view.string.applyToCheckedOneLevel destination lines.level |>.toOption
  pure {
    numberChanges := view.number.withChanges.map fun item =>
      (item.targetField, item.value)
    stringChanges := view.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    numberCleared := view.number.cleared
    stringCleared := view.string.cleared
    stringErrors := view.string.withErrors.map fun item =>
      (item.targetField, item.cause)
    baseAtFirst := numberApplied.stateAt { field := base.id, path := [1] }
    firstAtFirst := numberApplied.stateAt { field := first.id, path := [1] }
    firstAtSecond := numberApplied.stateAt { field := first.id, path := [2] }
    secondAtFirst := stringApplied.stateAt { field := second.id, path := [1] }
    secondAtSecond := stringApplied.stateAt { field := second.id, path := [2] }
    thirdAtFirst := numberApplied.stateAt { field := third.id, path := [1] }
    thirdAtSecond := numberApplied.stateAt { field := third.id, path := [2] }
    otherStringAtFirst :=
      stringApplied.stateAt { field := otherString.id, path := [1] }
  }

private structure RowView where
  coordinate : Nat
  firstTarget : CellAddr
  firstOutcome : NumericTargetOutcome
  secondTarget : CellAddr
  secondOutcome : StringTargetOutcome
  thirdTarget : CellAddr
  thirdOutcome : NumericTargetOutcome
  deriving Repr, DecidableEq

private def expectedRow (coordinate : Nat) (firstOutcome : NumericTargetOutcome)
    (secondOutcome : StringTargetOutcome)
    (thirdOutcome : NumericTargetOutcome) : RowView := {
  coordinate
  firstTarget := { field := first.id, path := [coordinate] }
  firstOutcome
  secondTarget := { field := second.id, path := [coordinate] }
  secondOutcome
  thirdTarget := { field := third.id, path := [coordinate] }
  thirdOutcome
}

private def rowOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List RowView) := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row => {
    coordinate := row.coordinate
    firstTarget := row.first.targetField
    firstOutcome := row.first.outcome
    secondTarget := row.second.targetField
    secondOutcome := row.second.outcome
    thirdTarget := row.third.targetField
    thirdOutcome := row.third.outcome
  })

private structure PhaseView where
  coordinates : List Nat
  number : List (CellAddr × NumericTargetOutcome)
  string : List (CellAddr × StringTargetOutcome)
  third : List (CellAddr × NumericTargetOutcome)
  deriving Repr, DecidableEq

private def phasedOutcomes? (firstBase : ClassifiedCellInput) :
    Option PhaseView := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let number <- plan.numberToString.executeNumberPhaseWithRead input input.read
    |>.toOption
  let string <- plan.numberToString.executeStringPhase prepared.patterns input number
    |>.toOption
  let third <- plan.executeThirdPhase input string |>.toOption
  pure {
    coordinates := number.coordinates
    number := number.outcomes.map fun outcome =>
      (outcome.targetField, outcome.outcome),
    string := string.map fun outcome => (outcome.targetField, outcome.outcome)
    third := third.map fun outcome => (outcome.targetField, outcome.outcome)
  }

private def encounterOrderOutcomes? :
    Option (List RowView) := do
  let plan <- plan?
  let cells := [3, 1, 2].flatMap fun row => [
    numericCell base.id row (row + 10),
    numericCell first.id row 70,
    stringCell second.id row "old",
    numericCell third.id row 700]
  let input <- checkedInput? [3, 1, 2] cells
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row => {
    coordinate := row.coordinate
    firstTarget := row.first.targetField
    firstOutcome := row.first.outcome
    secondTarget := row.second.targetField
    secondOutcome := row.second.outcome
    thirdTarget := row.third.targetField
    thirdOutcome := row.third.outcome
  })

private def stored (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

/- Analyze separates the structural coordinate from all three real field edges. -/
example :
    plan?.map CheckedCurrentRepetitionAlternatingChain.analyze = some {
      structuralGroup := lines.path
      scope := [lines.level]
      fieldDependencies := [
        (first.id, [base.id]),
        (second.id, [first.id]),
        (third.id, [second.id])]
    } := by
  native_decide

/- Both later steps consume same-run row-local state rather than either stale seed. -/
example :
    rowOutcomes? (numericCell base.id 1 7) = some [
      expectedRow 1 (.accepted { unscaled := 7, scale := 0 })
        (.accepted (stored "7" (by decide)))
        (.accepted { unscaled := 7, scale := 0 }),
      expectedRow 2 (.accepted { unscaled := 11, scale := 0 })
        (.accepted (stored "11" (by decide)))
        (.accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Each explicit phase retains its complete fresh predecessor before the next family reads it, rather than re-reading either stale seeded target. -/
example :
    phasedOutcomes? (numericCell base.id 1 7) = some {
      coordinates := [1, 2]
      number := [({ field := first.id, path := [1] },
          .accepted { unscaled := 7, scale := 0 }),
        ({ field := first.id, path := [2] },
          .accepted { unscaled := 11, scale := 0 })]
      string := [({ field := second.id, path := [1] },
          .accepted (stored "7" (by decide))),
        ({ field := second.id, path := [2] },
          .accepted (stored "11" (by decide)))]
      third := [({ field := third.id, path := [1] },
          .accepted { unscaled := 7, scale := 0 }),
        ({ field := third.id, path := [2] },
          .accepted { unscaled := 11, scale := 0 })]
    } := by
  native_decide

/- A wider finite input preserves physical encounter order. -/
example :
    encounterOrderOutcomes? = some [
      expectedRow 3 (.accepted { unscaled := 13, scale := 0 })
        (.accepted (stored "13" (by decide)))
        (.accepted { unscaled := 13, scale := 0 }),
      expectedRow 1 (.accepted { unscaled := 11, scale := 0 })
        (.accepted (stored "11" (by decide)))
        (.accepted { unscaled := 11, scale := 0 }),
      expectedRow 2 (.accepted { unscaled := 12, scale := 0 })
        (.accepted (stored "12" (by decide)))
        (.accepted { unscaled := 12, scale := 0 })] := by
  native_decide

/- Empty Number substitution reaches both typed edges as `0`, then `"0"`, then `0`. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := ""
      raw := .presentEmpty
    } = some [
      expectedRow 1 (.accepted { unscaled := 0, scale := 0 })
        (.accepted (stored "0" (by decide)))
        (.accepted { unscaled := 0, scale := 0 }),
      expectedRow 2 (.accepted { unscaled := 11, scale := 0 })
        (.accepted (stored "11" (by decide)))
        (.accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Malformed input poisons both later edges locally without aborting another row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    } = some [
      expectedRow 1 (.inheritedPoison .malformed)
        (.poison .computedDependency)
        (.inheritedPoison .computedDependency),
      expectedRow 2 (.accepted { unscaled := 11, scale := 0 })
        (.accepted (stored "11" (by decide)))
        (.accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- The String target error retains its attempted value and poisons only the reached Number. -/
example :
    rowOutcomes? (numericCell base.id 1 (-5)) = some [
      expectedRow 1 (.accepted { unscaled := -5, scale := 0 })
        (.errored (stored "-5" (by decide)) .pattern)
        (.inheritedPoison .computedDependency),
      expectedRow 2 (.accepted { unscaled := 11, scale := 0 })
        (.accepted (stored "11" (by decide)))
        (.accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- All three addressed phases project their changed rows and apply through the two established family carriers without a mixed document merge. -/
example : (do
    let input ← twoRowInput? (numericCell base.id 1 7)
    let destination ← twoRowInputWithTargets?
      (numericCell base.id 1 99) 70 "dest1" 700 110 "dest2" 1100
    resultApplicationSummary? input destination) = some {
      numberChanges := [
        ({ field := first.id, path := [1] },
          { unscaled := 7, scale := 0 }),
        ({ field := third.id, path := [1] },
          { unscaled := 7, scale := 0 }),
        ({ field := first.id, path := [2] },
          { unscaled := 11, scale := 0 }),
        ({ field := third.id, path := [2] },
          { unscaled := 11, scale := 0 })]
      stringChanges := [
        ({ field := second.id, path := [1] }, "7"),
        ({ field := second.id, path := [2] }, "11")]
      numberCleared := []
      stringCleared := []
      stringErrors := []
      baseAtFirst :=
        .presentValue (.decimal { unscaled := 99, scale := 0 })
      firstAtFirst :=
        .presentValue (.decimal { unscaled := 7, scale := 0 })
      firstAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
      secondAtFirst := .presentValue (stored "7" (by decide))
      secondAtSecond := .presentValue (stored "11" (by decide))
      thirdAtFirst :=
        .presentValue (.decimal { unscaled := 7, scale := 0 })
      thirdAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
      otherStringAtFirst := .presentValue (stored "KEEP" (by decide))
    } := by
  native_decide

/- Classification stays relative to the immutable computation source, so three source-identical successes remain inert against a different destination. -/
example : (do
    let input ← twoRowInputWithTargets?
      (numericCell base.id 1 7) 7 "7" 7 11 "11" 11
    let destination ← twoRowInputWithTargets?
      (numericCell base.id 1 99) 70 "dest1" 700 110 "dest2" 1100
    resultApplicationSummary? input destination) = some {
      numberChanges := []
      stringChanges := []
      numberCleared := []
      stringCleared := []
      stringErrors := []
      baseAtFirst :=
        .presentValue (.decimal { unscaled := 99, scale := 0 })
      firstAtFirst :=
        .presentValue (.decimal { unscaled := 70, scale := 0 })
      firstAtSecond :=
        .presentValue (.decimal { unscaled := 110, scale := 0 })
      secondAtFirst := .presentValue (stored "dest1" (by decide))
      secondAtSecond := .presentValue (stored "dest2" (by decide))
      thirdAtFirst :=
        .presentValue (.decimal { unscaled := 700, scale := 0 })
      thirdAtSecond :=
        .presentValue (.decimal { unscaled := 1100, scale := 0 })
      otherStringAtFirst := .presentValue (stored "KEEP" (by decide))
    } := by
  native_decide

/- Reached producer poison clears every source-filled row-one phase target while all three row-two successes remain changed and applicable. -/
example : (do
    let input ← twoRowInput? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    }
    resultApplicationSummary? input input) = some {
      numberChanges := [
        ({ field := first.id, path := [2] },
          { unscaled := 11, scale := 0 }),
        ({ field := third.id, path := [2] },
          { unscaled := 11, scale := 0 })]
      stringChanges := [({ field := second.id, path := [2] }, "11")]
      numberCleared := [
        { field := first.id, path := [1] },
        { field := third.id, path := [1] }]
      stringCleared := [{ field := second.id, path := [1] }]
      stringErrors := []
      baseAtFirst := .presentValue .nonComputedForm
      firstAtFirst := .presentEmpty
      firstAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
      secondAtFirst := .presentEmpty
      secondAtSecond := .presentValue (stored "11" (by decide))
      thirdAtFirst := .presentEmpty
      thirdAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
      otherStringAtFirst := .absent
    } := by
  native_decide

/- The middle String rejection remains ERRORED while the first Number value applies and the dependent third Number is cleared. -/
example : (do
    let input ← twoRowInput? (numericCell base.id 1 (-5))
    resultApplicationSummary? input input) = some {
      numberChanges := [
        ({ field := first.id, path := [1] },
          { unscaled := -5, scale := 0 }),
        ({ field := first.id, path := [2] },
          { unscaled := 11, scale := 0 }),
        ({ field := third.id, path := [2] },
          { unscaled := 11, scale := 0 })]
      stringChanges := [({ field := second.id, path := [2] }, "11")]
      numberCleared := [{ field := third.id, path := [1] }]
      stringCleared := []
      stringErrors := [({ field := second.id, path := [1] }, .pattern)]
      baseAtFirst :=
        .presentValue (.decimal { unscaled := -5, scale := 0 })
      firstAtFirst :=
        .presentValue (.decimal { unscaled := -5, scale := 0 })
      firstAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
      secondAtFirst := .presentEmpty
      secondAtSecond := .presentValue (stored "11" (by decide))
      thirdAtFirst := .presentEmpty
      thirdAtSecond :=
        .presentValue (.decimal { unscaled := 11, scale := 0 })
      otherStringAtFirst := .absent
    } := by
  native_decide

/- Wrong group, either bypassed edge, and both possible Number back-edges fail closed. -/
example :
    (match checkCurrentRepetitionAlternatingChain model lines.path otherGroup
        first.id (bare "BaseNumber") second.id (bare "FirstNumber")
        third.id (.direct (bare "SecondString")) with
      | .error (.numberToString (.groupMismatch source declaring)) =>
          source == other.path && declaring == lines.path
      | _ => false) = true ∧
    (match checkCurrentRepetitionAlternatingChain model lines.path group
        first.id (bare "BaseNumber") second.id (bare "BaseNumber")
        third.id (.direct (bare "SecondString")) with
      | .error (.numberToString (.dependency expected actual)) =>
          expected == first.id && actual == base.id
      | _ => false) = true ∧
    (match checkCurrentRepetitionAlternatingChain model lines.path group
        first.id (bare "BaseNumber") second.id (bare "FirstNumber")
        third.id (.direct (bare "OtherString")) with
      | .error (.dependency expected actual) =>
          expected == second.id && actual == otherString.id
      | _ => false) = true ∧
    (match checkCurrentRepetitionAlternatingChain model lines.path group
        first.id (bare "ThirdNumber") second.id (bare "FirstNumber")
        third.id (.direct (bare "SecondString")) with
      | .error (.cycle field) => field == third.id
      | _ => false) = true ∧
    (match checkCurrentRepetitionAlternatingChain model lines.path group
        first.id (bare "BaseNumber") second.id (bare "FirstNumber")
        first.id (.direct (bare "SecondString")) with
      | .error (.reverseDependency field) => field == first.id
      | _ => false) = true := by
  native_decide

/- No physical target row remains explicit insufficient information. -/
example :
    (do
      let plan <- plan?
      let input <- checkedInput? [] []
      pure (match plan.execute prepared.patterns input with
        | .error (.numberToString (.rowCardinality 0)) => true
        | _ => false)) = some true := by
  native_decide

private def transitionPlan : CheckedCurrentRepetitionAlternatingChain model :=
  plan?.get (by native_decide)

private def transitionNoRowsInput : CheckedDocument model :=
  (checkedInput? [] []).get (by native_decide)

private theorem transitionNoRowsNumberFailed :
    transitionPlan.numberToString.executeNumberPhaseWithRead
        transitionNoRowsInput transitionNoRowsInput.read =
      .error (.rowCardinality 0) := by
  rfl

/- The concrete no-row fault terminates in the initial state before any target
family completes. -/
example :
    CurrentRepetitionAlternatingChainFailureTransition transitionPlan
        prepared.patterns transitionNoRowsInput {}
        (.numberToString (.rowCardinality 0)) ∧
      CurrentRepetitionAlternatingChainFailureTrace transitionPlan
        prepared.patterns transitionNoRowsInput {}
        (.numberToString (.rowCardinality 0)) := by
  have failed : CurrentRepetitionAlternatingChainFailureTransition
      transitionPlan prepared.patterns transitionNoRowsInput {}
      (.numberToString (.rowCardinality 0)) :=
    .number (.rowCardinality 0) transitionNoRowsNumberFailed
  exact ⟨failed, .number failed⟩

private def transitionInput : CheckedDocument model :=
  (twoRowInput? (numericCell base.id 1 7)).get (by native_decide)

private def transitionNumberPhase :
    CurrentRepetitionNumberToStringNumberPhase :=
  (transitionPlan.numberToString.executeNumberPhaseWithRead transitionInput
    transitionInput.read).toOption.get (by native_decide)

private theorem evaluated_to_get (evaluation : Except ε α)
    (available : evaluation.toOption.isSome = true) :
    evaluation = .ok (evaluation.toOption.get available) := by
  cases evaluation with
  | error cause => simp [Except.toOption] at available
  | ok value => rfl

private theorem transitionNumberExecuted :
    transitionPlan.numberToString.executeNumberPhaseWithRead transitionInput
      transitionInput.read = .ok transitionNumberPhase := by
  simpa [transitionNumberPhase] using evaluated_to_get
    (evaluation :=
      transitionPlan.numberToString.executeNumberPhaseWithRead transitionInput
        transitionInput.read) (by native_decide)

private def missingPatternMatchers :
    PreparedFlatStringPatterns model builtinStringPatternCompiler := {
  fields := []
  modelWellFormed := by native_decide
}

private theorem transitionStringFailed :
    transitionPlan.numberToString.executeStringPhase missingPatternMatchers
        transitionInput transitionNumberPhase =
      .error (.string (.evaluation
        (.targetPatternUnavailable second.id))) := by
  rfl

private theorem transitionExecutionFailed :
    transitionPlan.execute missingPatternMatchers transitionInput =
      .error (.numberToString (.string (.evaluation
        (.targetPatternUnavailable second.id)))) := by
  unfold CheckedCurrentRepetitionAlternatingChain.execute
  rw [transitionNumberExecuted]
  simp only [Except.mapError, Bind.bind, Except.bind, transitionStringFailed]

/- The concrete missing-matcher fault retains the exact successful Number phase
instead of resetting the alternating chain to its initial state. -/
example :
    CurrentRepetitionAlternatingChainFailureTrace transitionPlan
      missingPatternMatchers transitionInput
      { number := some transitionNumberPhase }
      (.numberToString (.string (.evaluation
        (.targetPatternUnavailable second.id)))) := by
  exact .string
    (.number transitionNumberPhase transitionNumberExecuted)
    (.string transitionNumberPhase _ transitionStringFailed)

private def transitionStringPhase :
    List (SourcedStringTargetOutcome CellAddr) :=
  (transitionPlan.numberToString.executeStringPhase prepared.patterns
    transitionInput transitionNumberPhase).toOption.get (by native_decide)

private theorem transitionStringExecuted :
    transitionPlan.numberToString.executeStringPhase prepared.patterns
        transitionInput transitionNumberPhase = .ok transitionStringPhase := by
  simpa [transitionStringPhase] using evaluated_to_get
    (evaluation := transitionPlan.numberToString.executeStringPhase
      prepared.patterns transitionInput transitionNumberPhase)
    (by native_decide)

/- A terminal structural Number fault is conditional for this fixture. If it
occurs, the trace retains both exact successful prefix phases and no terminal
Number completion. -/
example (fault : CurrentRepetitionAlternatingChainFault)
    (thirdFailed :
      transitionPlan.executeThirdPhase transitionInput transitionStringPhase =
        .error fault) :
    CurrentRepetitionAlternatingChainFailureTrace transitionPlan
      prepared.patterns transitionInput
      { number := some transitionNumberPhase,
        string := some transitionStringPhase }
      fault := by
  exact .third
    (.number transitionNumberPhase transitionNumberExecuted)
    (.string transitionNumberPhase transitionStringPhase
      transitionStringExecuted)
    (.third transitionNumberPhase transitionStringPhase fault thirdFailed)

private def nestedPath : GroupPath := ["Shipment", "Lines", "Entries"]

private def nestedModel : FlatModel := {
  fields := [
    { base with groupPath := nestedPath, repeatableScope := [10, 20] },
    { first with groupPath := nestedPath, repeatableScope := [10, 20] },
    { second with groupPath := nestedPath, repeatableScope := [10, 20] },
    { third with groupPath := nestedPath, repeatableScope := [10, 20] }]
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
    Option (CheckedCurrentRepetitionAlternatingChain nestedModel) :=
  (checkCurrentRepetitionAlternatingChain nestedModel nestedPath nestedGroup
    first.id (bare "BaseNumber") second.id (bare "FirstNumber") third.id
    (.direct (bare "SecondString"))).toOption

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedNumericCell (field : FieldId) (path : List Nat)
    (value : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def nestedStringCell (path : List Nat) : ClassifiedCellInput := {
  address := { field := second.id, path }
  stored := "old"
  raw := .parsed (.str "old")
}

private def nestedInput? (middleBase : ClassifiedCellInput) :
    Option (CheckedDocument nestedModel) :=
  (checkDocument nestedPrepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      nestedNumericCell base.id [1, 1] 7,
      middleBase,
      nestedNumericCell base.id [1, 2] 13,
      nestedNumericCell first.id [1, 1] 70,
      nestedNumericCell first.id [2, 1] 110,
      nestedNumericCell first.id [1, 2] 130,
      nestedStringCell [1, 1],
      nestedStringCell [2, 1],
      nestedStringCell [1, 2],
      nestedNumericCell third.id [1, 1] 700,
      nestedNumericCell third.id [2, 1] 1100,
      nestedNumericCell third.id [1, 2] 1300]
  }).toOption

private def nestedRowOutcomes? (middleBase : ClassifiedCellInput) :
    Option (List RowView) := do
  let plan ← nestedPlan?
  let input ← nestedInput? middleBase
  let outcomes ← plan.execute nestedPrepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row => {
    coordinate := row.coordinate
    firstTarget := row.first.targetField
    firstOutcome := row.first.outcome
    secondTarget := row.second.targetField
    secondOutcome := row.second.outcome
    thirdTarget := row.third.targetField
    thirdOutcome := row.third.outcome
  })

private def expectedNestedRow (path : List Nat) (coordinate : Nat)
    (firstOutcome : NumericTargetOutcome) (secondOutcome : StringTargetOutcome)
    (thirdOutcome : NumericTargetOutcome) : RowView := {
  coordinate
  firstTarget := { field := first.id, path }
  firstOutcome
  secondTarget := { field := second.id, path }
  secondOutcome
  thirdTarget := { field := third.id, path }
  thirdOutcome
}

/- A valid two-level model retains its complete scope and all three typed field edges. -/
example :
    nestedPlan?.map CheckedCurrentRepetitionAlternatingChain.analyze = some {
          structuralGroup := nestedPath
          scope := [10, 20]
          fieldDependencies := [
            (first.id, [base.id]),
            (second.id, [first.id]),
            (third.id, [second.id])]
        } := by
  native_decide

/- The terminal coordinate stays distinct from the complete exact address while both later steps consume fresh nested state. -/
example :
    nestedRowOutcomes? (nestedNumericCell base.id [2, 1] 11) = some [
      expectedNestedRow [1, 1] 1 (.accepted { unscaled := 7, scale := 0 })
        (.accepted (stored "7" (by decide)))
        (.accepted { unscaled := 7, scale := 0 }),
      expectedNestedRow [2, 1] 1 (.accepted { unscaled := 11, scale := 0 })
        (.accepted (stored "11" (by decide)))
        (.accepted { unscaled := 11, scale := 0 }),
      expectedNestedRow [1, 2] 2 (.accepted { unscaled := 13, scale := 0 })
        (.accepted (stored "13" (by decide)))
        (.accepted { unscaled := 13, scale := 0 })] := by
  native_decide

/- Empty substitution remains local when another leaf under a different parent has the same terminal coordinate. -/
example :
    nestedRowOutcomes? {
      address := { field := base.id, path := [2, 1] }
      stored := ""
      raw := .presentEmpty
    } = some [
      expectedNestedRow [1, 1] 1 (.accepted { unscaled := 7, scale := 0 })
        (.accepted (stored "7" (by decide)))
        (.accepted { unscaled := 7, scale := 0 }),
      expectedNestedRow [2, 1] 1 (.accepted { unscaled := 0, scale := 0 })
        (.accepted (stored "0" (by decide)))
        (.accepted { unscaled := 0, scale := 0 }),
      expectedNestedRow [1, 2] 2 (.accepted { unscaled := 13, scale := 0 })
        (.accepted (stored "13" (by decide)))
        (.accepted { unscaled := 13, scale := 0 })] := by
  native_decide

/- An invalid leaf poisons only its exact nested state chain, including beside another leaf with the same terminal coordinate. -/
example :
    nestedRowOutcomes? {
      address := { field := base.id, path := [2, 1] }
      stored := "bad"
      raw := .rejected .malformed
    } = some [
      expectedNestedRow [1, 1] 1 (.accepted { unscaled := 7, scale := 0 })
        (.accepted (stored "7" (by decide)))
        (.accepted { unscaled := 7, scale := 0 }),
      expectedNestedRow [2, 1] 1 (.inheritedPoison .malformed)
        (.poison .computedDependency)
        (.inheritedPoison .computedDependency),
      expectedNestedRow [1, 2] 2 (.accepted { unscaled := 13, scale := 0 })
        (.accepted (stored "13" (by decide)))
        (.accepted { unscaled := 13, scale := 0 })] := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionAlternatingChain
