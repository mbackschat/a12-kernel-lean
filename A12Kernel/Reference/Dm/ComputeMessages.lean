import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Elaboration.OverRepetitionFindings

/-! # A computation call's formal-error channel, through the reader

One checked call reports a single message stream beside its outcomes (`spec/09` §3.3): the formal
findings of its selected uncomputed operand cells, the generated index findings at selected index
operands, the over-repetition findings its prepared data retains, and the value-less error of every
computed target that produced no instance. Messages at a computed instance are absorbed, and the
residual is the channel the Kernel reports as `formalErrorsInOperands`. Each message is projected to
its rendered pointer and runtime code; payloads are not rendered.

The checked cell keeps a coarse cause, so a declaration-dependent code is recomputed from the
placement's stored input through the declaration's own cascade, the one that produced the cause. A
cause no projection names surfaces as `?` and its cause, so a replay row exposes it rather than
dropping it.
-/

namespace A12Kernel.Dm

/-- One message of a computation call's formal-error channel: its pointer and runtime code. -/
structure ComputedMessage where
  pointer : String
  code : String
  deriving Repr, BEq, Ord, Inhabited

instance : ToString ComputedMessage where
  toString message := s!"{message.pointer}:{message.code}"

private def overRepetitionCode : OverRepetitionCode → String
  | .serialNumberTooLarge => AddressRefusal.serialTooLarge.code
  | .rowNumberTooLarge => AddressRefusal.rowTooLarge.code
  | .contextNumberTooLarge => AddressRefusal.contextTooLarge.code

/-- The code a declaration-dependent cause carries, recomputed from the placement's stored input. -/
private def recomputedCode (model : FlatModel)
    (patterns : PreparedFlatStringPatterns model compilePattern) (placement : CheckedCellPlacement) :
    FormalCause → Option String
  | .leadingOrTrailingSpace => do
      (← universalFormalRefusal? model.legalCharset.accepts (← placement.storedText)).errorCode
  | .malformed | .declaredConstraint => do
      let declaration ← model.fields.find? (·.id == placement.address.field)
      match declaration.policy.kind with
      | .number info =>
          match declaration.numericTargetConstraints.checkFormalRead info (← placement.numericInput) with
          | .error error => some error.errorCode
          | .ok _ => none
      | .string =>
          match declaration.stringPolicy.checkTextWithPattern (← patterns.targetMatcher? declaration.id)
              (← placement.storedText) with
          | .error error => some error.errorCode
          | .ok _ => none
      -- An unrecognized token draws the String pattern class
      -- ([checkpoint](../../../docs/sources/having-filter-probes.md#src-presence-leaf-operand-kinds), `four-code-families-report-and-do-not-abort`).
      | .enumeration => some StringFieldError.pattern.errorCode
      | _ => none
  | .registeredCustomValidation rejection => some rejection.projectCode
  | _ => none

/-- A cell finding's message, or none for the coarse over-repetition entry the structural findings
replace with their positional codes. -/
private def findingMessage (model : FlatModel) (patterns : PreparedFlatStringPatterns model compilePattern)
    (checked : CheckedDocument model) (finding : ComputationFormalInputFinding) : Option ComputedMessage :=
  let code? := match finding.cause with
    | .overRepetition => none
    | .required => some IndexPreliminaryKind.mandatory.errorCode
    | .duplicateIndex => some IndexPreliminaryKind.unique.errorCode
    | .unsupportedCharacter => some UniversalFormalRefusal.characterNotInCharset.errorCode
    | cause =>
      let placement? := checked.checkedCells.find? fun (placement : CheckedCellPlacement) =>
        placement.address == finding.address
      some ((cause.fixedFormalErrorCode? <|> placement?.bind (recomputedCode model patterns · cause)).getD
        s!"?{reprStr cause}")
  code?.map fun code => { pointer := renderPointer model (MessagePointer.ofCellAddr finding.address), code }

private def structuralPointer (model : FlatModel) : OverRepetitionNode → Option RulePointer
  | .cell address => some (MessagePointer.ofCellAddr address)
  | .row address => do
      let declared ← model.repeatableGroupAtLevel? address.group
      pure { entity := .group declared.path, coordinates := address.path.map .concrete }
  | .group occurrence =>
      some { entity := .group occurrence.path, coordinates := occurrence.coordinates.map .concrete }

/-- The pointer of a computed target, whether it produced an instance, and whether it carries the
value-less target error. -/
private def targetReport : MixedComputationOutcome → CellAddr × Bool × Bool
  | .number entry => (entry.targetField, entry.outcome.hasComputedInstance, entry.outcome.emitsValuelessTargetError)
  | .string target outcome =>
      ({ field := target, path := [] }, outcome.hasComputedInstance, outcome == .invalidNoValue)
  | .document address outcome =>
      (address, outcome.storedText?.isSome || (documentAttempt? outcome).isSome,
        (outcome.formalValueMessage? (MessagePointer.ofCellAddr address)).isSome)

/-- The residual formal-error channel of one checked call, sorted, since order is not compared. A plan
whose input selection does not bind has no channel, though its run already required that binding. -/
def computationMessages (model : FlatModel) (patterns : PreparedFlatStringPatterns model compilePattern)
    (checked : CheckedDocument model) (plan : CheckedMixedComputationPlan model compilePattern)
    (result : MixedComputationCheckedResult) : Option (List ComputedMessage) := do
  let inputPlan ← plan.formalInputPlan.toOption
  let pointer (address : CellAddr) := renderPointer model (MessagePointer.ofCellAddr address)
  let targets := result.outcomes.map targetReport
  let structural := (inputPlan.structuralFindings checked).filterMap fun finding =>
    (structuralPointer model finding.node).map fun at_ =>
      { pointer := renderPointer model at_, code := overRepetitionCode finding.code }
  let valueless := targets.filterMap fun (address, _, valueless) =>
    if valueless then some { pointer := pointer address, code := berechnungsWertFehler } else none
  let instances := targets.filterMap fun (address, produced, _) => if produced then some (pointer address) else none
  let messages := result.formalErrorsInOperands.filterMap (findingMessage model patterns checked) ++
    structural ++ valueless
  pure ((messages.filter (!instances.contains ·.pointer)).mergeSort (compare · · != .gt))

/-- Run the complete model and return its outcomes beside its formal-error channel. -/
def runModelComputationsWithMessages (model : DmModel) (language : Language) (world : World)
    (prepared : PreparedFlatStringContext model.flat compilePattern)
    (checked : CheckedDocument model.flat) : Lowering (List ComputedOutcome × List ComputedMessage) := do
  let lowered ← lowerModelComputations model language
  if lowered.isEmpty then return ([], [])
  let (plan, result) ← runCheckedComputations world prepared checked lowered
  let some messages := computationMessages model.flat prepared.patterns checked plan result
    | throw { construct := "ComputationRun", detail := "the plan's formal-input selection does not bind" }
  pure (projectOutcomes checked result, messages)

end A12Kernel.Dm
