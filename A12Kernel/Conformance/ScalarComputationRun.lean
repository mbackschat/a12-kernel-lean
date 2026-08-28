import A12Kernel.Elaboration.ScalarComputationFormalInput
import A12Kernel.Elaboration.ScalarComputationRunRelation

/-! # Finite mixed scalar computation-run locks

The matrix alternates checked String and Number tables in both directions. It separates typed completed overlays from stale source state, ordinary input reads, reached poison, an unread dependency, structural-fault family and target attribution, and the supplied-order plan gates.
-/

namespace A12Kernel.Conformance.ScalarComputationRun

open A12Kernel

private def inputStringId : FieldId := 0
private def inputNumberId : FieldId := 1
private def firstStringId : FieldId := 2
private def firstNumberId : FieldId := 3
private def secondStringId : FieldId := 4
private def secondNumberId : FieldId := 5
private def gateId : FieldId := 6

private def stringDeclaration (id : FieldId) (name : String)
    (numeric : Bool := false) : FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .string }
  stringPolicy := if numeric then { maxLength := some 15 } else {}
  stringPatternSource := if numeric then some "[0-9]+" else none

private def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel :=
  { fields := [
      stringDeclaration inputStringId "InputString" true,
      numberDeclaration inputNumberId "InputNumber",
      stringDeclaration firstStringId "FirstString" true,
      numberDeclaration firstNumberId "FirstNumber",
      stringDeclaration secondStringId "SecondString",
      numberDeclaration secondNumberId "SecondNumber",
      stringDeclaration gateId "Gate"] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def stringTable? (target : FieldId)
    (rows : List (ComputationCondition × StringExpr SurfaceFieldPath)) :
    Option (CheckedStringComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← (elaborateStringComputationOperation
      model ["Form"] target expression).toOption
    pure ({ precondition := guard, operation } :
      ComputationAlternative (CheckedStringComputationOperation model))
  (certifyStringComputationTable alternatives).toOption

private def numberTable? (target : FieldId)
    (rows : List
      (ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom)) :
    Option (CheckedNumericComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← (elaborateNumericTargetComputationOperation
      model ["Form"] target expression).toOption
    pure ({ precondition := guard, operation } :
      ComputationAlternative
        (CheckedNumericTargetComputationOperation model))
  (certifyNumericComputationTable alternatives).toOption

private def literalNumber (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def asNumber (field : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber (.direct (bare field)))

private def numberField (field : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (bare field))

private def holding : ComputationCondition := .fieldNotFilled gateId

private def always : ComputationCondition :=
  .or (.fieldFilled gateId) (.fieldNotFilled gateId)

private def firstStringValue :=
  (stringTable? firstStringId [(holding, .literal "7")]).get
    (by native_decide)

private def emptyFirstString :=
  (stringTable? firstStringId [
    (.fieldFilled gateId, .literal "7")]).get
      (by native_decide)

private def invalidFirstString :=
  (stringTable? firstStringId [(holding, .literal "BAD")]).get
    (by native_decide)

private def firstNumberFromString :=
  (numberTable? firstNumberId [(holding,
    .binary .add (asNumber "FirstString")
      (asNumber "InputString"))]).get (by native_decide)

private def firstNumberFromStringOnly :=
  (numberTable? firstNumberId [(holding,
    asNumber "FirstString")]).get (by native_decide)

private def firstNumberUnreadString :=
  (numberTable? firstNumberId [
    (holding, literalNumber 3),
    (holding, asNumber "FirstString")]).get (by native_decide)

private def firstNumberUnreadInputString :=
  (numberTable? firstNumberId [
    (holding, literalNumber 3),
    (holding, asNumber "InputString")]).get (by native_decide)

private def secondStringFromNumber :=
  (stringTable? secondStringId [(holding,
    .concat (.fieldValueAsString (bare "FirstNumber"))
      (.concat (.literal "/")
        (.fieldValueAsString (bare "InputNumber"))))]).get
          (by native_decide)

private def secondStringFromNumberOnly :=
  (stringTable? secondStringId [(holding,
    .fieldValueAsString (bare "FirstNumber"))]).get
      (by native_decide)

private def firstNumberValue :=
  (numberTable? firstNumberId [(holding, literalNumber 7)]).get
    (by native_decide)

private def firstStringFromNumber :=
  (stringTable? firstStringId [(holding,
    .fieldValueAsString (bare "FirstNumber"))]).get
      (by native_decide)

private def consumerFirst :=
  (stringTable? secondStringId [
    (.fieldFilled gateId, .literal "SAFE"),
    (.fieldNotFilled gateId,
      .fieldValueAsString (bare "FirstNumber"))]).get
        (by native_decide)

private def producerSecond :=
  (numberTable? firstNumberId [(always,
    numberField "InputNumber")]).get (by native_decide)

private def secondNumberFromString :=
  (numberTable? secondNumberId [(holding,
    .binary .add (asNumber "FirstString")
      (asNumber "InputString"))]).get (by native_decide)

private def stringCell (field : FieldId) (stored : String) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.str stored) }

private def numberCell (field : FieldId) (amount : Int) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

private def malformedNumberCell (field : FieldId) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := "bad"
    raw := .rejected .malformed }

private def malformedStringCell (field : FieldId) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := "bad"
    raw := .rejected .malformed }

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private def outcomes? (steps : List (CheckedScalarComputationStep model))
    (cells : List ClassifiedCellInput := []) :
    Option (List ScalarComputationOutcome) := do
  let run ← (certifyScalarComputationRun steps).toOption
  let input ← checkedDocument cells
  (run.execute world prepared.patterns input).toOption

private def fault?
    (steps : List (CheckedScalarComputationStep model))
    (patterns : PreparedFlatStringPatterns model builtinStringPatternCompiler) :
    Option ScalarComputationRunFault := do
  let run ← (certifyScalarComputationRun steps).toOption
  let input ← checkedDocument []
  match run.execute world patterns input with
  | .error fault => some fault
  | .ok _ => none

private def missingPatterns :
    PreparedFlatStringPatterns model builtinStringPatternCompiler := {
  fields := []
  modelWellFormed := by native_decide
}

private def pairTargetOrders?
    (first second : CheckedScalarComputationStep model) :
    Option (List FieldId × List FieldId) := do
  let pair ← (certifyScalarComputationPair first second).toOption
  pure (pair.authoredTargetFields, pair.executionTargetFields)

private def pairOutcomes?
    (first second : CheckedScalarComputationStep model)
    (cells : List ClassifiedCellInput := []) :
    Option (List ScalarComputationOutcome) := do
  let pair ← (certifyScalarComputationPair first second).toOption
  let input ← checkedDocument cells
  (pair.execute world prepared.patterns input).toOption

private def stringNumberString : List (CheckedScalarComputationStep model) :=
  [.string firstStringValue,
    .number firstNumberFromString,
    .string secondStringFromNumber]

private def numberStringNumber : List (CheckedScalarComputationStep model) :=
  [.number firstNumberValue,
    .string firstStringFromNumber,
    .number secondNumberFromString]

private structure ResultSummary where
  stringWithoutErrors : List (FieldId × String)
  stringWithChanges : List (FieldId × String)
  stringErrors : List (FieldId × String × StringTargetError)
  stringCleared : List FieldId
  numberWithoutErrors : List (FieldId × StoredNumber)
  numberWithChanges : List (FieldId × StoredNumber)
  numberCleared : List FieldId
  deriving Repr, DecidableEq

private def resultSummary?
    (steps : List (CheckedScalarComputationStep model))
    (cells : List ClassifiedCellInput := []) :
    Option ResultSummary := do
  let run ← (certifyScalarComputationRun steps).toOption
  let input ← checkedDocument cells
  let view ← (run.executeResult world prepared.patterns input
    (fun _ => ()) [] ([] : List Unit)).toOption
  pure {
    stringWithoutErrors := view.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    stringWithChanges := view.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    stringErrors := view.string.withErrors.map fun item =>
      (item.targetField, item.attempted.text, item.cause)
    stringCleared := view.string.cleared
    numberWithoutErrors := view.number.withoutErrors.map fun item =>
      (item.targetField, item.value)
    numberWithChanges := view.number.withChanges.map fun item =>
      (item.targetField, item.value)
    numberCleared := view.number.cleared
  }

/- Both alternating orders consume completed typed values instead of stale target cells, while ordinary String and Number reads stay on the immutable document paths. -/
example :
    outcomes? stringNumberString [
      stringCell inputStringId "2",
      numberCell inputNumberId 4,
      stringCell firstStringId "8",
      numberCell firstNumberId 80,
      stringCell secondStringId "OLD"] =
      some [
        .string firstStringId (.accepted { text := "7", nonempty := by decide }),
        .number firstNumberId (.accepted { unscaled := 9, scale := 0 }),
        .string secondStringId
          (.accepted { text := "9/4", nonempty := by decide })] ∧
    outcomes? numberStringNumber [
      stringCell inputStringId "2",
      numberCell firstNumberId 80,
      stringCell firstStringId "8",
      numberCell secondNumberId 90] =
      some [
        .number firstNumberId (.accepted { unscaled := 7, scale := 0 }),
        .string firstStringId (.accepted { text := "7", nonempty := by decide }),
        .number secondNumberId
          (.accepted { unscaled := 9, scale := 0 })] := by
  native_decide

/- A structural fault in the later String step retains that step's family and target rather than inheriting the run's first target. The same run with its complete prepared-pattern set is the positive control. -/
example :
    fault? [.number firstNumberValue, .string firstStringValue]
        missingPatterns =
      some (.string (.evaluation firstStringId
        (.targetPatternUnavailable firstStringId))) ∧
    (fault? [.number firstNumberValue, .string firstStringValue]
      missingPatterns).map ScalarComputationRunFault.target =
        some firstStringId ∧
    (fault? [.number firstNumberValue, .string firstStringValue]
      missingPatterns).map ScalarComputationRunFault.targetKind = some .string ∧
    fault? [.number firstNumberValue, .string firstStringValue]
        prepared.patterns = none := by
  native_decide

/- Each family result owner independently classifies the same successful mixed run relative to the immutable source. -/
example :
    resultSummary? stringNumberString [
      stringCell inputStringId "2",
      numberCell inputNumberId 4,
      stringCell firstStringId "8",
      numberCell firstNumberId 80,
      stringCell secondStringId "OLD"] =
      some {
        stringWithoutErrors :=
          [(firstStringId, "7"), (secondStringId, "9/4")]
        stringWithChanges :=
          [(firstStringId, "7"), (secondStringId, "9/4")]
        stringErrors := []
        stringCleared := []
        numberWithoutErrors :=
          [(firstNumberId, { unscaled := 9, scale := 0 })]
        numberWithChanges :=
          [(firstNumberId, { unscaled := 9, scale := 0 })]
        numberCleared := []
      } ∧
    resultSummary? numberStringNumber [
      stringCell inputStringId "2",
      numberCell firstNumberId 7,
      stringCell firstStringId "7",
      numberCell secondNumberId 9] =
      some {
        stringWithoutErrors := [(firstStringId, "7")]
        stringWithChanges := []
        stringErrors := []
        stringCleared := []
        numberWithoutErrors := [
          (firstNumberId, { unscaled := 7, scale := 0 }),
          (secondNumberId, { unscaled := 9, scale := 0 })]
        numberWithChanges := []
        numberCleared := []
      } := by
  native_decide

/- Clean String no-selection clears only the stale String producer. Its reached Number conversion stores zero, and the final String stores that Number's canonical text. -/
example :
    resultSummary? [
      .string emptyFirstString,
      .number firstNumberFromStringOnly,
      .string secondStringFromNumberOnly] [
        stringCell firstStringId "8",
        numberCell firstNumberId 80,
        stringCell secondStringId "OLD"] =
      some {
        stringWithoutErrors := [(secondStringId, "0")]
        stringWithChanges := [(secondStringId, "0")]
        stringErrors := []
        stringCleared := [firstStringId]
        numberWithoutErrors :=
          [(firstNumberId, { unscaled := 0, scale := 0 })]
        numberWithChanges :=
          [(firstNumberId, { unscaled := 0, scale := 0 })]
        numberCleared := []
      } := by
  native_decide

/- Payloadful String rejection stays in the String error channel; the two inherited-poison targets have no computed instances and clear their own stale source values. -/
example :
    resultSummary? [
      .string invalidFirstString,
      .number firstNumberFromStringOnly,
      .string secondStringFromNumberOnly] [
        stringCell firstStringId "8",
        numberCell firstNumberId 80,
        stringCell secondStringId "OLD"] =
      some {
        stringWithoutErrors := []
        stringWithChanges := []
        stringErrors := [(firstStringId, "BAD", .pattern)]
        stringCleared := [secondStringId]
        numberWithoutErrors := []
        numberWithChanges := []
        numberCleared := [firstNumberId]
      } := by
  native_decide

/- Reached invalidity crosses both family boundaries as cause-blind poison. An earlier selected Number row leaves the same later syntactic conversion unread, so the final String remains valid. -/
example :
    outcomes? [
      .string invalidFirstString,
      .number firstNumberFromStringOnly,
      .string secondStringFromNumberOnly] =
      some [
        .string firstStringId
          (.errored { text := "BAD", nonempty := by decide } .pattern),
        .number firstNumberId
          (.inheritedPoison .computedDependency),
        .string secondStringId (.poison .computedDependency)] ∧
    outcomes? [
      .string invalidFirstString,
      .number firstNumberUnreadString,
      .string secondStringFromNumberOnly] =
      some [
        .string firstStringId
          (.errored { text := "BAD", nonempty := by decide } .pattern),
        .number firstNumberId
          (.accepted { unscaled := 3, scale := 0 }),
        .string secondStringId
          (.accepted { text := "3", nonempty := by decide })] := by
  native_decide

/- Mixed plans require preconsolidated unique targets and backward-only dependencies. -/
example :
    (certifyScalarComputationRun [
      .string firstStringValue,
      .string firstStringValue]).toOption = none ∧
    (certifyScalarComputationRun [
      .number firstNumberFromStringOnly,
      .string firstStringValue]).toOption = none := by
  native_decide

/- A two-step authored pair retains its original order for Analyze while Execute reverses only the forward dependency and therefore reads the producer's fresh completion instead of stale target state. -/
example :
    pairTargetOrders? (.string firstStringFromNumber)
        (.number firstNumberValue) =
      some ([firstStringId, firstNumberId],
        [firstNumberId, firstStringId]) ∧
    pairOutcomes? (.string firstStringFromNumber)
        (.number firstNumberValue) [
          numberCell firstNumberId 80,
          stringCell firstStringId "8"] =
      some [
        .number firstNumberId
          (.accepted { unscaled := 7, scale := 0 }),
        .string firstStringId
          (.accepted { text := "7", nonempty := by decide })] := by
  native_decide

/- An already backward-dependent pair and an independent pair retain supplied order; a mutual dependency is not repaired by swapping. -/
example :
    pairTargetOrders? (.number firstNumberValue)
        (.string firstStringFromNumber) =
      some ([firstNumberId, firstStringId],
        [firstNumberId, firstStringId]) ∧
    pairTargetOrders? (.string firstStringValue)
        (.number firstNumberValue) =
      some ([firstStringId, firstNumberId],
        [firstStringId, firstNumberId]) ∧
    (certifyScalarComputationPair
      (.string firstStringFromNumber)
      (.number firstNumberFromStringOnly)).toOption = none := by
  native_decide

/- The kernel-calibrated consumer-first representative reads the fresh producer, preserves an unread invalid producer behind the selected safe row, poisons a reached read, and treats empty Number input as zero. -/
example :
    pairOutcomes? (.string consumerFirst) (.number producerSecond) [
      numberCell inputNumberId 7,
      numberCell firstNumberId 80,
      stringCell secondStringId "OLD"] =
      some [
        .number firstNumberId
          (.accepted { unscaled := 7, scale := 0 }),
        .string secondStringId
          (.accepted { text := "7", nonempty := by decide })] ∧
    pairOutcomes? (.string consumerFirst) (.number producerSecond) [
      malformedNumberCell inputNumberId,
      stringCell gateId "open"] =
      some [
        .number firstNumberId (.inheritedPoison .malformed),
        .string secondStringId
          (.accepted { text := "SAFE", nonempty := by decide })] ∧
    pairOutcomes? (.string consumerFirst) (.number producerSecond) [
      malformedNumberCell inputNumberId] =
      some [
        .number firstNumberId (.inheritedPoison .malformed),
        .string secondStringId (.poison .computedDependency)] ∧
    pairOutcomes? (.string consumerFirst) (.number producerSecond) =
      some [
        .number firstNumberId
          (.accepted { unscaled := 0, scale := 0 }),
        .string secondStringId
          (.accepted { text := "0", nonempty := by decide })] := by
  native_decide

private def independentSteps : List (CheckedScalarComputationStep model) :=
  [.string firstStringValue, .number firstNumberValue]

private def independentRun : CheckedScalarComputationRun model :=
  (certifyScalarComputationRun independentSteps).toOption.get (by native_decide)

private def independentInput : CheckedDocument model :=
  (checkedDocument []).get (by native_decide)

private theorem evaluated_to_get (evaluation : Except ε α)
    (available : evaluation.toOption.isSome = true) :
    evaluation = .ok (evaluation.toOption.get available) := by
  cases evaluation with
  | error cause => simp [Except.toOption] at available
  | ok value => rfl

private def stringFirst :=
  (independentRun.evaluateStep world prepared.patterns independentInput {}
    (.string firstStringValue)).toOption.get (by native_decide)
private def afterString : ScalarComputationRunState := { completed := [stringFirst] }
private def numberAfterString :=
  (independentRun.evaluateStep world prepared.patterns independentInput
    afterString (.number firstNumberValue)).toOption.get (by native_decide)
private def stringThenNumber : ScalarComputationRunState :=
  { completed := [stringFirst, numberAfterString] }

private def numberFirst :=
  (independentRun.evaluateStep world prepared.patterns independentInput {}
    (.number firstNumberValue)).toOption.get (by native_decide)
private def afterNumber : ScalarComputationRunState := { completed := [numberFirst] }
private def stringAfterNumber :=
  (independentRun.evaluateStep world prepared.patterns independentInput
    afterNumber (.string firstStringValue)).toOption.get (by native_decide)
private def numberThenString : ScalarComputationRunState :=
  { completed := [numberFirst, stringAfterNumber] }

private theorem stringFirst_evaluated :
    independentRun.evaluateStep world prepared.patterns independentInput {}
      (.string firstStringValue) = .ok stringFirst := by
  simpa [stringFirst] using evaluated_to_get
    (evaluation := independentRun.evaluateStep world prepared.patterns
      independentInput {} (.string firstStringValue)) (by native_decide)

private theorem numberAfterString_evaluated :
    independentRun.evaluateStep world prepared.patterns independentInput
      afterString (.number firstNumberValue) = .ok numberAfterString := by
  simpa [numberAfterString] using evaluated_to_get
    (evaluation := independentRun.evaluateStep world prepared.patterns
      independentInput afterString (.number firstNumberValue)) (by native_decide)

private theorem numberFirst_evaluated :
    independentRun.evaluateStep world prepared.patterns independentInput {}
      (.number firstNumberValue) = .ok numberFirst := by
  simpa [numberFirst] using evaluated_to_get
    (evaluation := independentRun.evaluateStep world prepared.patterns
      independentInput {} (.number firstNumberValue)) (by native_decide)

private theorem stringAfterNumber_evaluated :
    independentRun.evaluateStep world prepared.patterns independentInput
      afterNumber (.string firstStringValue) = .ok stringAfterNumber := by
  simpa [stringAfterNumber] using evaluated_to_get
    (evaluation := independentRun.evaluateStep world prepared.patterns
      independentInput afterNumber (.string firstStringValue)) (by native_decide)

private theorem independent_enabled
    (step : CheckedScalarComputationStep model)
    (state : ScalarComputationRunState)
    (notString : step.referencesField firstStringId = false)
    (notNumber : step.referencesField firstNumberId = false) :
    ScalarComputationDependenciesEnabled independentRun step state := by
  intro dependency member referenced
  have targets :
      independentRun.targetFields = [firstStringId, firstNumberId] := by
    native_decide
  rw [targets] at member
  simp at member
  rcases member with rfl | rfl
  · rw [notString] at referenced
    contradiction
  · rw [notNumber] at referenced
    contradiction

/- Independent typed steps are enabled in either order, and target-indexed rich outcomes erase their private completion order. -/
example :
    ScalarComputationRunTransition independentRun world prepared.patterns
        independentInput {} stringFirst.outcome afterString ∧
    ScalarComputationRunTransition independentRun world prepared.patterns
        independentInput afterString numberAfterString.outcome stringThenNumber ∧
    ScalarComputationRunTransition independentRun world prepared.patterns
        independentInput {} numberFirst.outcome afterNumber ∧
    ScalarComputationRunTransition independentRun world prepared.patterns
        independentInput afterNumber stringAfterNumber.outcome numberThenString ∧
    (stringThenNumber.find? firstStringId).map (·.outcome) =
        (numberThenString.find? firstStringId).map (·.outcome) ∧
    (stringThenNumber.find? firstNumberId).map (·.outcome) =
        (numberThenString.find? firstNumberId).map (·.outcome) := by
  constructor
  · exact .compute (.string firstStringValue) (by
      change .string firstStringValue ∈ independentSteps
      simp [independentSteps])
      (by native_decide)
      (independent_enabled _ _ (by native_decide) (by native_decide))
      stringFirst stringFirst_evaluated
  constructor
  · exact .compute (.number firstNumberValue) (by
      change .number firstNumberValue ∈ independentSteps
      simp [independentSteps])
      (by native_decide)
      (independent_enabled _ _ (by native_decide) (by native_decide))
      numberAfterString
      numberAfterString_evaluated
  constructor
  · exact .compute (.number firstNumberValue) (by
      change .number firstNumberValue ∈ independentSteps
      simp [independentSteps])
      (by native_decide)
      (independent_enabled _ _ (by native_decide) (by native_decide))
      numberFirst numberFirst_evaluated
  constructor
  · exact .compute (.string firstStringValue) (by
      change .string firstStringValue ∈ independentSteps
      simp [independentSteps])
      (by native_decide)
      (independent_enabled _ _ (by native_decide) (by native_decide))
      stringAfterNumber
      stringAfterNumber_evaluated
  native_decide

private def dependentRun : CheckedScalarComputationRun model :=
  (certifyScalarComputationRun [
    .string firstStringValue, .number firstNumberUnreadString])
      |>.toOption |>.get (by native_decide)

private def dependentProducer :=
  (dependentRun.evaluateStep world prepared.patterns independentInput {}
    (.string firstStringValue)).toOption.get (by native_decide)

/- Static dependency readiness disables the Number consumer before its String producer and enables it after completion even though the consumer's first selected literal leaves its later dependency read unreached. -/
example :
    ¬ ScalarComputationDependenciesEnabled dependentRun
        (.number firstNumberUnreadString) {} ∧
      ScalarComputationDependenciesEnabled dependentRun
        (.number firstNumberUnreadString) { completed := [dependentProducer] } := by
  constructor
  · intro enabled
    have completed := enabled firstStringId (by native_decide) (by native_decide)
    simp [ScalarComputationRunState.targetFields] at completed
  · intro dependency member referenced
    have targets :
        dependentRun.targetFields = [firstStringId, firstNumberId] := by
      native_decide
    rw [targets] at member
    simp at member
    rcases member with rfl | rfl
    · native_decide
    · have selfExcluded :
          CheckedScalarComputationStep.referencesField
            (.number firstNumberUnreadString) firstNumberId = false := by
        native_decide
      rw [selfExcluded] at referenced
      contradiction

private def failingStringRun : CheckedScalarComputationRun model :=
  (certifyScalarComputationRun [.string firstStringValue])
    |>.toOption |>.get (by native_decide)

private def missingStringPatternFault : ScalarComputationRunFault :=
  .string (.evaluation firstStringId
    (.targetPatternUnavailable firstStringId))

private theorem failingString_evaluated :
    failingStringRun.evaluateStep world missingPatterns independentInput {}
      (.string firstStringValue) = .error missingStringPatternFault := by
  rfl

/- A structural failure is a terminal transition of its enabled typed step and leaves the successful-prefix state unchanged. -/
example :
    ScalarComputationRunFailureTransition failingStringRun world
        missingPatterns independentInput {} missingStringPatternFault ∧
      ScalarComputationRunFailureTrace failingStringRun world
        missingPatterns independentInput {} [] {} missingStringPatternFault := by
  have member :
      CheckedScalarComputationStep.string firstStringValue ∈
        failingStringRun.steps := by
    change CheckedScalarComputationStep.string firstStringValue ∈
      [CheckedScalarComputationStep.string firstStringValue]
    simp
  have pending : firstStringId ∉ ({} : ScalarComputationRunState).targetFields := by
    simp [ScalarComputationRunState.targetFields]
  have enabled : ScalarComputationDependenciesEnabled failingStringRun
      (.string firstStringValue) {} := by
    intro dependency dependencyMember referenced
    have onlyTarget : failingStringRun.targetFields = [firstStringId] := by
      native_decide
    rw [onlyTarget] at dependencyMember
    simp at dependencyMember
    subst dependency
    have selfExcluded :
        CheckedScalarComputationStep.referencesField
          (.string firstStringValue) firstStringId = false := by
      native_decide
    rw [selfExcluded] at referenced
    contradiction
  have failed : ScalarComputationRunFailureTransition failingStringRun world
      missingPatterns independentInput {} missingStringPatternFault :=
    .fail (.string firstStringValue) member pending enabled
      failingString_evaluated
  exact ⟨failed, .failed failed⟩

private def formalFinding (field : FieldId)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := { field, path := [] }
  cause
}

private structure MixedFormalInputSummary where
  planOperands : List FieldId
  planTargets : List FieldId
  selectedFields : List FieldId
  findings : List ComputationFormalInputFinding
  stringValues : List (FieldId × String)
  numberValues : List (FieldId × StoredNumber)
  deriving Repr, DecidableEq

private def mixedFormalInputSummary? : Option MixedFormalInputSummary := do
  let run ← (certifyScalarComputationRun [
    .number firstNumberUnreadInputString,
    .string secondStringFromNumber]).toOption
  let input ← checkedDocument [
    malformedStringCell inputStringId,
    numberCell inputNumberId 4,
    stringCell secondStringId "OLD"]
  let plan ← run.formalInputPlan.toOption
  let view ← (run.executeResultWithFormalInputs world prepared.patterns input
    (fun _ => ()) [] ([] : List Unit)).toOption
  pure {
    planOperands := plan.operandFields
    planTargets := plan.computedFields
    selectedFields := plan.selectedFields
    findings := view.formalErrorsInOperands
    stringValues := view.scalar.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    numberValues := view.scalar.number.withoutErrors.map fun item =>
      (item.targetField, item.value)
  }

/- The mixed plan inventories every family's raw dependencies, excludes both computed targets, and retains an eager malformed hidden alternative beside the exact family-partitioned result. -/
example : mixedFormalInputSummary? = some {
    planOperands := [inputStringId, gateId, inputNumberId, firstNumberId]
    planTargets := [firstNumberId, secondStringId]
    selectedFields := [inputStringId, gateId, inputNumberId]
    findings := [formalFinding inputStringId .malformed]
    stringValues := [(secondStringId, "3/4")]
    numberValues := [
      (firstNumberId, { unscaled := 3, scale := 0 })]
  } := by
  native_decide

private def mixedFormalFailure? :
    Option (List ComputationFormalInputFinding × FieldId × SurfaceScalarKind) := do
  let run ← (certifyScalarComputationRun [
    .number firstNumberUnreadInputString,
    .string firstStringValue]).toOption
  let input ← checkedDocument [malformedStringCell inputStringId]
  match run.executeResultWithFormalInputs world missingPatterns input
      (fun _ => ()) [] ([] : List Unit) with
  | .error (.execution findings (.execution fault)) =>
      some (findings, fault.target, fault.targetKind)
  | _ => none

/- A later typed structural fault retains the same eager mixed input inventory and its own String target identity. -/
example : mixedFormalFailure? = some (
    [formalFinding inputStringId .malformed], firstStringId, .string) := by
  native_decide

end A12Kernel.Conformance.ScalarComputationRun
