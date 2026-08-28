import A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

/-! # Generated-computation alternative and phase locks -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.Alternatives

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable
open A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

private def formalInputTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation crossGroupModel)) := do
  let first ← crossGroupNumberOperation.toOption
  let second ← crossGroupDatePartOperation.toOption
  pure {
    targetField := crossGroupTarget.id
    name := "computedFormalInputs"
    commonPrecondition := some (.fieldFilled crossGroupOtherTarget.id)
    alternatives := .guarded {
      first := {
        precondition := .fieldFilled crossGroupSource.id
        operation := first }
      second := {
        precondition := .fieldNotFilled crossGroupExtra.id
        operation := second } }
    messagePlan
  }

private def formalInputPrepared : PreparedFlatStringContext crossGroupModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
    crossGroupModel).toOption.get (by native_decide)

private def rejectedInput (field : FieldId) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored := "x"
  raw := .rejected .malformed
}

private def formalInputDocument? : Option (CheckedDocument crossGroupModel) :=
  (checkDocument formalInputPrepared "en_US" {
    instantiatedRows := []
    cells := [
      rejectedInput crossGroupSource.id,
      rejectedInput crossGroupDate.id,
      rejectedInput crossGroupExtra.id,
      rejectedInput crossGroupTarget.id,
      rejectedInput crossGroupOtherTarget.id,
      rejectedInput crossGroupDateTime.id]
  }).toOption

private def invalidCommonFormalInputError? :
    Option GeneratedNumericComputationFormalInputPlanError := do
  let table ← formalInputTable?
  match { table with
      commonPrecondition := some (.fieldFilled 999) }.formalInputPlan with
  | .error error => some error
  | .ok _ => none

private def generatedRuntimeContext
    (common source extra date : RawCell) : ScalarComputationContext :=
  let raw : RawFlatContext := {
    read field :=
      if field = crossGroupOtherTarget.id then common
      else if field = crossGroupSource.id then source
      else if field = crossGroupExtra.id then extra
      else if field = crossGroupDate.id then date
      else .empty
  }
  { read := (crossGroupModel.checkContext raw).read }

private def domainFailureOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation crossGroupModel) :=
  elaborateNumericComputationOperation crossGroupModel ["Rules"]
    crossGroupTarget.id
    (.binary .divide
      (.literal { value := 1, authoredScale := 0 })
      (.literal { value := 0, authoredScale := 0 })) true

private def domainFailureFirstTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation crossGroupModel)) := do
  let first ← domainFailureOperation.toOption
  let second ← crossGroupNumberOperation.toOption
  pure {
    targetField := crossGroupTarget.id
    name := "domainFailureFirst"
    commonPrecondition := some (.fieldFilled crossGroupOtherTarget.id)
    alternatives := .guarded {
      first := {
        precondition := .fieldFilled crossGroupSource.id
        operation := first }
      second := {
        precondition := .fieldFilled crossGroupSource.id
        operation := second } }
    messagePlan
  }

private def operationPoisonTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation crossGroupModel)) := do
  let first ← crossGroupNumberOperation.toOption
  let second ← crossGroupDatePartOperation.toOption
  pure {
    targetField := crossGroupTarget.id
    name := "operationPoison"
    commonPrecondition := some (.fieldFilled crossGroupOtherTarget.id)
    alternatives := .guarded {
      first := {
        precondition := .fieldFilled crossGroupExtra.id
        operation := first }
      second := {
        precondition := .fieldNotFilled crossGroupExtra.id
        operation := second } }
    messagePlan
  }

private def generatedRuntimeResult
    (common source extra date : RawCell) :
    Option GeneratedNumericComputationEvaluation := do
  let table ← formalInputTable?
  (table.evaluateNumeric
    (generatedRuntimeContext common source extra date)).toOption

private def domainFailureFirstResult :
    Option GeneratedNumericComputationEvaluation := do
  let table ← domainFailureFirstTable?
  (table.evaluateNumeric (generatedRuntimeContext
    (.parsed (.num 1)) (.parsed (.num 7)) .empty .empty)).toOption

private def invalidRuntimeCommonValidationError? :
    Option GeneratedComputationValidationError := do
  let table ← formalInputTable?
  match { table with
      commonPrecondition := some (.fieldFilled 999) }.evaluateNumeric
        (generatedRuntimeContext (.parsed (.num 1))
          (.parsed (.num 7)) .empty .empty) with
  | .error (.validation error) => some error
  | .error (.operation _) | .error (.targetPolicyUnavailable _) | .ok _ => none

private def selectedOperationPoisonResult :
    Option GeneratedNumericComputationEvaluation := do
  let table ← operationPoisonTable?
  (table.evaluateNumeric (generatedRuntimeContext
    (.parsed (.num 1)) (.rejected .malformed)
      (.parsed (.num 1)) .empty)).toOption

private def generatedRuntimeTargetPolicy : NumericTargetPolicy :=
  crossGroupTarget.toNumericTargetPolicy?.get (by native_decide)

private def generatedRuntimeTargetResult
    (common source extra date : RawCell) : Option NumericTargetCheckResult := do
  let table ← formalInputTable?
  (table.evaluateNumericTarget
    (generatedRuntimeContext common source extra date)).toOption

private def policyBoundSource : FlatFieldDecl :=
  { id := 40, groupPath := ["Input"], name := "PolicySource",
    policy := { kind := .number { scale := 0, signed := true } } }

private def policyBoundTarget : FlatFieldDecl :=
  { id := 41, groupPath := ["Output"], name := "PolicyTarget",
    policy := { kind := .number { scale := 0, signed := true } },
    numericTargetConstraints := {
      NumericTargetConstraints.unconstrained with zeroAllowed := false } }

private def policyBoundModel : FlatModel :=
  { fields := [policyBoundSource, policyBoundTarget] }

private def policyBoundOperation : Except NumericComputationElabError
    (CheckedNumericComputationOperation policyBoundModel) :=
  elaborateNumericComputationOperation policyBoundModel ["Rules"]
    policyBoundTarget.id
    (.atom (.field (absolutePath ["Input"] "PolicySource")))

private def policyBoundTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation policyBoundModel)) := do
  let operation ← policyBoundOperation.toOption
  pure {
    targetField := policyBoundTarget.id
    name := "policyBound"
    alternatives := .singleton { operation }
    messagePlan
  }

private def policyBoundZeroResult : Option NumericTargetCheckResult := do
  let table ← policyBoundTable?
  let raw : RawFlatContext := {
    read field :=
      if field = policyBoundSource.id then .parsed (.num 0) else .empty
  }
  (table.evaluateNumericTarget {
    read := (policyBoundModel.checkContext raw).read }).toOption

/- Runtime evaluation preserves activation and operation phases: a false common
   guard hides malformed row inputs, common poison stops before selection, and a
   selected operand poison stays an operation result. -/
example :
    generatedRuntimeResult .empty (.rejected .malformed)
        (.rejected .malformed) (.rejected .malformed) =
        some .noMatch := by
  native_decide

example :
    generatedRuntimeResult (.rejected .malformed) (.parsed (.num 7))
      .empty .empty = some (.guardPoison .malformed) := by
  native_decide

example :
    generatedRuntimeResult (.parsed (.num 1)) (.parsed (.num 7))
      (.rejected .malformed) (.rejected .malformed) =
        some (.evaluated false (.value 7)) := by
  native_decide

example :
    selectedOperationPoisonResult =
      some (.evaluated false (.poison .malformed)) := by
  native_decide

/- First selection is final even when the selected numeric operation has a
   domain failure; the later holding operation is not evaluated as fallback. -/
example : domainFailureFirstResult =
    some (.evaluated true .domainFailure) := by
  native_decide

/- Target completion preserves the activation partition and dispatches a
   selected result through that operation's exact warning-suppression choice. -/
example :
    GeneratedNumericComputationEvaluation.noMatch.completeNumericTarget
        generatedRuntimeTargetPolicy = .supported .noValue ∧
      ((GeneratedNumericComputationEvaluation.guardPoison .malformed)
        |>.completeNumericTarget generatedRuntimeTargetPolicy) =
          .supported (.inheritedPoison .malformed) ∧
      ((GeneratedNumericComputationEvaluation.evaluated false .domainFailure)
        |>.completeNumericTarget generatedRuntimeTargetPolicy) =
          .supported (.invalidNoValue .calculationValue) := by
  native_decide

example :
    ((GeneratedNumericComputationEvaluation.evaluated false
        (.value (24723 / 10000)))
      |>.completeNumericTarget generatedRuntimeTargetPolicy) =
        .unsupported (.fractionalScaleDoesNotFit 4 0) ∧
      ((GeneratedNumericComputationEvaluation.evaluated true
        (.value (24723 / 10000)))
      |>.completeNumericTarget generatedRuntimeTargetPolicy) =
        .supported (.rejected
          { unscaled := 24723, scale := 4 } .suppressedScaleMismatch) := by
  native_decide

/- Whole target evaluation binds the table's own declaration policy while
   preserving every established activation and selected-result outcome. -/
example :
    generatedRuntimeTargetResult .empty (.rejected .malformed)
        (.rejected .malformed) (.rejected .malformed) =
        some (.supported .noValue) ∧
      generatedRuntimeTargetResult (.rejected .malformed)
        (.parsed (.num 7)) .empty .empty =
          some (.supported (.inheritedPoison .malformed)) ∧
      generatedRuntimeTargetResult (.parsed (.num 1))
        (.parsed (.num 7)) .empty .empty =
          some (.supported (.accepted { unscaled := 7, scale := 0 })) ∧
      operationPoisonTable?.bind (fun table =>
        (table.evaluateNumericTarget (generatedRuntimeContext
          (.parsed (.num 1)) (.rejected .malformed)
            (.parsed (.num 1)) .empty)).toOption) =
          some (.supported (.inheritedPoison .malformed)) ∧
      domainFailureFirstTable?.bind (fun table =>
        (table.evaluateNumericTarget (generatedRuntimeContext
          (.parsed (.num 1)) (.parsed (.num 7)) .empty .empty)).toOption) =
          some (.supported (.invalidNoValue .calculationValue)) := by
  native_decide

/- The whole route cannot substitute an unconstrained caller policy for the
   generated target declaration's zero prohibition. -/
example : policyBoundZeroResult = some (.supported (.rejected
    { unscaled := 0, scale := 0 } .zeroNotAllowed)) := by
  native_decide

/- Runtime cannot bypass the generated table's existing model and guard
   admission merely because selection could otherwise evaluate the raw syntax. -/
example : invalidRuntimeCommonValidationError? = some
    (.resolve (.unknownFieldId 999)) := by
  native_decide

/- Semantic desugaring derives the checked condition's row group from the resolved computation target declaration. -/
example : generatedRowGroupOf bothHoldingDifferent = some ["Form"] := by
  native_decide

private def tolerateFirst (range : NumericToleranceRange)
    (candidate : LiteralNumberComputation) : LiteralNumberComputation :=
  match candidate.alternatives with
  | .singleton alternative =>
      { candidate with alternatives := .singleton {
          alternative with tolerance := some range } }
  | .guarded alternatives =>
      { candidate with alternatives := .guarded {
          alternatives with
          first := { alternatives.first with tolerance := some range } } }

/- Computation selects the first holding operation, while generated validation retains the later holding mismatch. -/
example :
    selectionOf bothHoldingDifferent
        (bothFilled (.parsed (.num 1))) = .selected (literal 1) ∧
      outcomeOf bothHoldingDifferent
        (bothFilled (.parsed (.num 1))) =
          some (.fired (expectedMessage .value)) := by
  native_decide

/- The sole alternative may omit its precondition: computation selects it directly, while generated validation compares it without fabricating a guard. -/
example :
    let candidate := singletonComputation none 3
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 3) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some (.fired (expectedMessage .value)) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 3))) =
        some .notFired := by
  native_decide

/- A singleton's own guard and the table-wide common guard independently suppress both consumers when false. -/
example :
    let guarded := singletonComputation (some (.fieldNotFilled gate.id)) 3
    let commonGuarded :=
      { singletonComputation none 3 with
        commonPrecondition := some (.fieldNotFilled gate.id) }
    selectionOf guarded (bothFilled (.parsed (.num 1))) = .noMatch ∧
      outcomeOf guarded (bothFilled (.parsed (.num 1))) = some .notFired ∧
      selectionOf commonGuarded (bothFilled (.parsed (.num 1))) = .noMatch ∧
      outcomeOf commonGuarded (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- A third guarded alternative remains in declaration order for both first-match selection and all-alternatives validation. -/
example :
    let candidate :=
      guardedComputation
        (alternative (.fieldNotFilled gate.id) 90)
        (alternative (.fieldNotFilled gate.id) 91)
        [alternative (.fieldFilled gate.id) 3]
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 3) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Equal results under the same overlapping guard do not create a mismatch. -/
example :
    let candidate :=
      computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 1
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- Per-alternative tolerance changes only the generated mismatch: computation still selects the literal operation, while interior and boundary differences stay quiet and a strict exterior fires. -/
example :
    let candidate := tolerateFirst .range1 <|
      computation (.fieldFilled gate.id) 1 (.fieldNotFilled gate.id) 99
    selectionOf candidate (bothFilled (.parsed (.num 2))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num (3 / 2)))) =
        some .notFired ∧
      outcomeOf candidate (bothFilled (.parsed (.num 2))) =
        some .notFired ∧
      outcomeOf candidate (bothFilled (.parsed (.num 3))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Tolerance is tier-local: a tolerant first mismatch does not soften a later strict alternative. -/
example :
    let candidate := tolerateFirst .range10 <|
      computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 20
    outcomeOf candidate (bothFilled (.parsed (.num 10))) =
      some (.fired (expectedMessage .value)) := by
  native_decide

/- A nonholding second guard cannot make its different operation reject the selected result. -/
example :
    let candidate :=
      computation (.fieldFilled gate.id) 1 (.fieldNotFilled gate.id) 2
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- A cleanly false common precondition suppresses both computation selection and the complete generated mismatch disjunction. -/
example :
    let candidate :=
      { bothHoldingDifferent with
        commonPrecondition := some (.fieldNotFilled gate.id) }
    selectionOf candidate (bothFilled (.parsed (.num 2))) = .noMatch ∧
      outcomeOf candidate (bothFilled (.parsed (.num 2))) =
        some .notFired := by
  native_decide

/- A holding common precondition preserves first-match computation while generated validation still retains the later holding mismatch. -/
example :
    let candidate :=
      { bothHoldingDifferent with
        commonPrecondition := some (.fieldFilled gate.id) }
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- The admitted generated table contributes its common guard, every row guard,
   and every checked operation to one target-excluding formal-input plan. -/
example :
    (do
      let table ← formalInputTable?
      let plan ← table.formalInputPlan.toOption
      let input ← formalInputDocument?
      pure (table.fieldDependencies, plan.operandFields,
        plan.computedFields, plan.findings input)) =
      some ([crossGroupSource.id, crossGroupDate.id, crossGroupExtra.id,
          crossGroupOtherTarget.id],
        [crossGroupSource.id, crossGroupDate.id, crossGroupExtra.id,
          crossGroupOtherTarget.id],
        [crossGroupTarget.id],
        [
          { address := { field := crossGroupSource.id, path := [] },
            cause := .malformed },
          { address := { field := crossGroupDate.id, path := [] },
            cause := .malformed },
          { address := { field := crossGroupExtra.id, path := [] },
            cause := .malformed },
          { address := { field := crossGroupOtherTarget.id, path := [] },
            cause := .malformed }
        ]) := by
  native_decide

/- Formal-input projection cannot silently erase an unknown common guard: the
   existing generated-table admission boundary rejects it first. -/
example :
    invalidCommonFormalInputError? = some
      (.validation (.resolve (.unknownFieldId 999))) := by
  native_decide

/- A malformed common guard preserves the phase split before any alternative-specific guard contributes. -/
example :
    let candidate :=
      { bothHoldingDifferent with
        commonPrecondition := some (.fieldFilled broken.id) }
    selectionOf candidate brokenAndHealthy = .poison .malformed ∧
      outcomeOf candidate brokenAndHealthy = some .unknown := by
  native_decide

/- An authored conjunction remains a conjunction in generated validation; one false conjunct keeps the differing first row silent. -/
example :
    let firstGuard :=
      ComputationCondition.and
        (.fieldFilled gate.id) (.fieldNotFilled gate.id)
    let candidate :=
      computation firstGuard 2 (.fieldFilled gate.id) 1
    selectionOf candidate (bothFilled (.parsed (.num 1))) =
        .selected (literal 1) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 1))) =
        some .notFired := by
  native_decide

/- The explicit target-filled gate suppresses every mismatch when the target is empty. -/
example :
    selectionOf bothHoldingDifferent (bothFilled .empty) =
        .selected (literal 1) ∧
      outcomeOf bothHoldingDifferent (bothFilled .empty) =
        some .notFired := by
  native_decide

/- The same guard syntax has phase-specific consumers: computation poison aborts, while validation `Or` lets a healthy firing branch dominate unknown. -/
example :
    let guarded :=
      ComputationCondition.or (.fieldFilled broken.id) (.fieldFilled gate.id)
    let candidate :=
      computation guarded 2 (.fieldNotFilled gate.id) 1
    selectionOf candidate brokenAndHealthy = .poison .malformed ∧
      outcomeOf candidate brokenAndHealthy =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Message polarity remains data-derived: a not-filled guard can make this ERROR an OMISSION. -/
example :
    let candidate :=
      computation (.fieldNotFilled gate.id) 2 (.fieldFilled gate.id) 1
    selectionOf candidate gateEmptyTargetOne = .selected (literal 2) ∧
      outcomeOf candidate gateEmptyTargetOne =
        some (.fired (expectedMessage .omission)) := by
  native_decide

/- Swapping both literal results supplies an independent instance of the overlap mechanism. -/
example :
    let candidate :=
      computation (.fieldFilled gate.id) 2 (.fieldFilled gate.id) 1
    selectionOf candidate (bothFilled (.parsed (.num 2))) =
        .selected (literal 2) ∧
      outcomeOf candidate (bothFilled (.parsed (.num 2))) =
        some (.fired (expectedMessage .value)) := by
  native_decide

/- Authored numeric scale remains checked before the literal value is erased into the flat comparison. -/
example :
    let singletonMismatch :=
      { singletonComputation none 1 with alternatives := .singleton {
          operation := { value := 1, authoredScale := 1 } } }
    let firstMismatch :=
      guardedComputation {
          precondition := .fieldFilled gate.id
          operation := { value := 1, authoredScale := 1 }
        } (alternative (.fieldFilled gate.id) 2)
    let secondMismatch :=
      guardedComputation (alternative (.fieldFilled gate.id) 1) {
          precondition := .fieldFilled gate.id
          operation := { value := 2, authoredScale := 1 }
        }
    let thirdMismatch :=
      guardedComputation (alternative (.fieldFilled gate.id) 1)
        (alternative (.fieldFilled gate.id) 2) [{
          precondition := .fieldFilled gate.id
          operation := { value := 3, authoredScale := 1 }
        }]
    assemblyErrorOf singletonMismatch =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf
        { singletonMismatch with
          commonPrecondition := some (.fieldFilled target.id) } =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf firstMismatch =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf secondMismatch =
        some (.operationScaleMismatch 2 0 1) ∧
      assemblyErrorOf thirdMismatch =
        some (.operationScaleMismatch 3 0 1) := by
  native_decide

/- A tolerance alternative bypasses the ordinary exact-comparison scale gate. -/
example :
    let singletonMismatch :=
      { singletonComputation none 1 with alternatives := .singleton {
          operation := { value := 1, authoredScale := 1 }
          tolerance := some .range1 } }
    let firstMismatch :=
      guardedComputation {
          precondition := .fieldFilled gate.id
          operation := { value := 1, authoredScale := 1 }
          tolerance := some .range1
        } (alternative (.fieldFilled gate.id) 2)
    let thirdMismatch :=
      guardedComputation (alternative (.fieldFilled gate.id) 1)
        (alternative (.fieldFilled gate.id) 2) [{
          precondition := .fieldFilled gate.id
          operation := { value := 3, authoredScale := 1 }
          tolerance := some .range1
        }]
    (assembleGeneratedLiteralNumberRule model singletonMismatch).isOk = true ∧
      (assembleGeneratedLiteralNumberRule model firstMismatch).isOk = true ∧
      (assembleGeneratedLiteralNumberRule model thirdMismatch).isOk = true := by
  native_decide

/- String presence guards are consumed in both phases without widening the Number target or table shape. -/
example :
    let candidate :=
      computation (.fieldFilled textGuard.id) 2
        (.fieldNotFilled textGuard.id) 1
    selectionOf candidate
        (textGuardTargetOne (.parsed (.str "present"))) =
        .selected (literal 2) ∧
      outcomeOf candidate
        (textGuardTargetOne (.parsed (.str "present"))) =
        some (.fired (expectedMessage .value)) ∧
      selectionOf candidate (textGuardTargetOne .presentEmpty) =
        .selected (literal 1) ∧
      outcomeOf candidate (textGuardTargetOne .presentEmpty) =
        some .notFired := by
  native_decide

/- A malformed String guard preserves the established phase split: computation poisons while generated validation is unknown. -/
example :
    let candidate :=
      computation (.fieldFilled textGuard.id) 2
        (.fieldNotFilled textGuard.id) 2
    selectionOf candidate (textGuardTargetOne (.rejected .malformed)) =
        .poison .malformed ∧
      outcomeOf candidate (textGuardTargetOne (.rejected .malformed)) =
        some .unknown := by
  native_decide

/- The generated fragment still rejects a non-Number target. -/
example :
    assemblyErrorOf
      { bothHoldingDifferent with targetField := broken.id } =
      some (.targetNotNumber broken.id) := by
  native_decide

/- The computed target cannot appear in the common or any alternative precondition; diagnostics retain the authored guard position. -/
example :
    assemblyErrorOf
        { bothHoldingDifferent with
          commonPrecondition := some
            (.and (.fieldFilled gate.id)
              (.or (.fieldNotFilled broken.id) (.fieldFilled target.id))) } =
        some (.targetSelfReference .common) ∧
      assemblyErrorOf
        (guardedComputation (alternative (.fieldFilled target.id) 1)
          (alternative (.fieldFilled gate.id) 2)) =
        some (.targetSelfReference (.alternative 1)) ∧
      assemblyErrorOf
        (guardedComputation (alternative (.fieldFilled gate.id) 1)
          (alternative (.fieldFilled gate.id) 2)
          [alternative (.fieldFilled target.id) 3]) =
        some (.targetSelfReference (.alternative 3)) ∧
      assemblyErrorOf
        (singletonComputation (some (.fieldFilled target.id)) 1) =
        some (.targetSelfReference (.alternative 1)) := by
  native_decide

/- The direct-ID route rejects repeatable guard and target declarations before constructing a flat rule. -/
example :
    assemblyErrorIn repeatableModel
        (computation (.fieldFilled repeatedGate.id) 1
          (.fieldFilled gate.id) 2) =
        some (.resolve (.repeatableReference repeatedGate.path)) ∧
      assemblyErrorIn repeatableModel
        { bothHoldingDifferent with targetField := repeatedTarget.id } =
        some (.resolve (.repeatableReference repeatedTarget.path)) ∧
      assemblyErrorIn repeatableModel
        { bothHoldingDifferent with
          commonPrecondition := some (.fieldFilled repeatedGate.id) } =
        some (.resolve (.repeatableReference repeatedGate.path)) ∧
      assemblyErrorIn repeatableModel
        (guardedComputation (alternative (.fieldFilled gate.id) 1)
          (alternative (.fieldFilled gate.id) 2)
          [alternative (.fieldFilled repeatedGate.id) 3]) =
        some (.resolve (.repeatableReference repeatedGate.path)) := by
  native_decide


end A12Kernel.Conformance.GeneratedComputationValidation.Alternatives
