import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Two-alternative generated-computation validation locks -/

namespace A12Kernel.Conformance.GeneratedComputationValidation

open A12Kernel

private def gate : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Gate",
    policy := { kind := .number { scale := 0, signed := true } } }

private def target : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } } }

private def broken : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Broken",
    policy := { kind := .boolean } }

private def textGuard : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "TextGuard",
    policy := { kind := .string } }

private def repeatedGate : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "Gate",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

private def repeatedTarget : FlatFieldDecl :=
  { id := 5, groupPath := ["Form", "Rows"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [gate, target, broken, textGuard] }

private def repeatableModel : FlatModel :=
  { fields := [
      gate, target, broken, textGuard, repeatedGate, repeatedTarget]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def messagePlan : MessageRenderPlan :=
  { parts := [.text "Target disagrees with the computation table"] }

private def text : ResolvedMessageText :=
  messagePlan.render

private def literal (value : Rat) : DecodedNumericLiteral :=
  { value, authoredScale := 0 }

private def alternative (precondition : ComputationCondition)
    (operation : Rat) : LiteralNumberComputationAlternative :=
  { precondition, operation := literal operation }

private def computation (firstGuard : ComputationCondition) (firstValue : Rat)
    (secondGuard : ComputationCondition) (secondValue : Rat) :
    TwoAlternativeLiteralNumberComputation :=
  { targetField := target.id
    name := "computedTarget"
    first := alternative firstGuard firstValue
    second := alternative secondGuard secondValue
    messagePlan }

private def bothFilled (targetCell : RawCell) : RawFlatContext where
  read field :=
    if field = gate.id then .parsed (.num 7)
    else if field = target.id then targetCell
    else .empty

private def gateEmptyTargetOne : RawFlatContext where
  read field :=
    if field = target.id then .parsed (.num 1)
    else .empty

private def textGuardTargetOne (textCell : RawCell) : RawFlatContext where
  read field :=
    if field = textGuard.id then textCell
    else if field = target.id then .parsed (.num 1)
    else .empty

private def brokenAndHealthy : RawFlatContext where
  read field :=
    if field = gate.id then .parsed (.num 7)
    else if field = target.id then .parsed (.num 1)
    else if field = broken.id then .rejected .malformed
    else .empty

private def selectionOf (candidate : TwoAlternativeLiteralNumberComputation)
    (raw : RawFlatContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  candidate.selectFirst { read := (model.checkContext raw).read }

private def outcomeOf (candidate : TwoAlternativeLiteralNumberComputation)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assembleGeneratedLiteralNumberRule model candidate with
  | .error _ => none
  | .ok rule => some (rule.evalFull raw true)

private def assemblyErrorIn (checkedModel : FlatModel)
    (candidate : TwoAlternativeLiteralNumberComputation) :
    Option GeneratedComputationValidationError :=
  match assembleGeneratedLiteralNumberRule checkedModel candidate with
  | .ok _ => none
  | .error error => some error

private def assemblyErrorOf :=
  assemblyErrorIn model

private def expectedMessage (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := target.id, path := [] }
    errorCode := "computedTarget"
    severity := .error
    messageType
    text }

private def bothHoldingDifferent : TwoAlternativeLiteralNumberComputation :=
  computation (.fieldFilled gate.id) 1 (.fieldFilled gate.id) 2

private def tolerateFirst (range : NumericToleranceRange)
    (candidate : TwoAlternativeLiteralNumberComputation) :
    TwoAlternativeLiteralNumberComputation :=
  { candidate with first := { candidate.first with tolerance := some range } }

/- Computation selects the first holding operation, while generated validation retains the later holding mismatch. -/
example :
    selectionOf bothHoldingDifferent
        (bothFilled (.parsed (.num 1))) = .selected (literal 1) ∧
      outcomeOf bothHoldingDifferent
        (bothFilled (.parsed (.num 1))) =
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
    let firstMismatch :=
      { bothHoldingDifferent with
        first := {
          precondition := .fieldFilled gate.id
          operation := { value := 1, authoredScale := 1 }
        } }
    let secondMismatch :=
      { bothHoldingDifferent with
        second := {
          precondition := .fieldFilled gate.id
          operation := { value := 2, authoredScale := 1 }
        } }
    assemblyErrorOf firstMismatch =
        some (.operationScaleMismatch 1 0 1) ∧
      assemblyErrorOf secondMismatch =
        some (.operationScaleMismatch 2 0 1) := by
  native_decide

/- A tolerance alternative bypasses the ordinary exact-comparison scale gate. -/
example :
    let firstMismatch :=
      { bothHoldingDifferent with
        first := {
          precondition := .fieldFilled gate.id
          operation := { value := 1, authoredScale := 1 }
          tolerance := some .range1
        } }
    (assembleGeneratedLiteralNumberRule model firstMismatch).isOk = true := by
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
        some (.resolve (.repeatableReference repeatedGate.path)) := by
  native_decide

end A12Kernel.Conformance.GeneratedComputationValidation
