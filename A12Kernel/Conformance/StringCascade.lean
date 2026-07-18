import A12Kernel.Semantics.StringApplication
import A12Kernel.Semantics.StringCascade

/-! # Direct String-cascade executable locks

These locks exercise one explicitly ordered producer-to-consumer edge. They do not introduce a dependency graph or infer scheduling from retained output order.
-/

namespace A12Kernel.Conformance.StringCascade

open A12Kernel

private def valueOf : Except ε α → Option α
  | .ok value => some value
  | .error _ => none

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def sourceId : FieldId := 1
private def midId : FieldId := 2
private def outId : FieldId := 3

private def checkedString (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (source mid : RawCell) : StringComputationContext where
  read field :=
    if field == sourceId then checkedString source
    else if field == midId then checkedString mid
    else checkedString .empty

private def storedAbc : StoredString := ⟨"ABC", by decide⟩
private def storedAbcd : StoredString := ⟨"ABCD", by decide⟩
private def storedOld : StoredString := ⟨"OLD", by decide⟩
private def storedAbcX : StoredString := ⟨"ABC-X", by decide⟩
private def storedDashX : StoredString := ⟨"-X", by decide⟩
private def storedOldX : StoredString := ⟨"OLD-X", by decide⟩

private def maxThree : StringTargetLengthPolicy := .maximum ⟨3, by decide⟩

private def cascade (midPrior outPrior : PriorStringTarget) : StringDirectCascade where
  producer := {
    targetField := midId
    expression := .field sourceId
    targetPolicy := maxThree
    prior := midPrior }
  consumer := {
    targetField := outId
    expression := .concat (.field midId) (.literal "-X")
    targetPolicy := .unconstrained
    prior := outPrior }

private def expected (producerOutcome : StringTargetOutcome)
    (producerDelta : Option StringDelta)
    (consumerOutcome : StringTargetOutcome)
    (consumerDelta : Option StringDelta) : StringDirectCascadeResult := {
  producer := { outcome := producerOutcome, delta := producerDelta }
  consumer := { outcome := consumerOutcome, delta := consumerDelta } }

/- A clean not-true common precondition skips the body even when reading that body would poison. -/
example : (cascade (.filled storedOld) (.filled storedOldX)).producer.evaluateOutcomeWhen
    .notTrue (context (.rejected .malformed) (.parsed (.str "OLD"))) =
      .ok .noValue := by
  rfl

/- With only the decision changed to holds, the same malformed source is consumed and poisons the producer. -/
example : (cascade (.filled storedOld) (.filled storedOldX)).producer.evaluateOutcomeWhen
    .holds (context (.rejected .malformed) (.parsed (.str "OLD"))) =
      .ok (.poison .malformed) := by
  rfl

/- A holding common precondition delegates to the ordinary accepted-body path. -/
example : valueOf
    ((cascade (.filled storedOld) (.filled storedOldX)).producer.evaluateOutcomeWhen
      .holds (context (.parsed (.str "ABC")) (.parsed (.str "OLD")))) =
        some (.accepted storedAbc) := by
  native_decide

/- A clean not-true common precondition suppresses the same otherwise accepted body. -/
example : (cascade (.filled storedOld) (.filled storedOldX)).producer.evaluateOutcomeWhen
    .notTrue (context (.parsed (.str "ABC")) (.parsed (.str "OLD"))) =
      .ok .noValue := by
  rfl

/- Quiet precondition clearing and consumed-operand poison have the same immediate target placement but remain different dependency reads. -/
example :
    StringTargetOutcome.noValue.applyTo (.presentValue storedOld) =
        (StringTargetOutcome.poison .malformed).applyTo (.presentValue storedOld) ∧
      valueOf ((context .empty .empty).withDependencyOutcome midId .noValue
          |>.map (fun updated => updated.readTerm midId)) ≠
        valueOf ((context .empty .empty).withDependencyOutcome midId (.poison .malformed)
          |>.map (fun updated => updated.readTerm midId)) := by
  constructor
  · rfl
  · change
      (some (.ok StringTerm.noValue) : Option (Except StringComputationFault StringTerm)) ≠
        some (.ok (.poison .malformed))
    simp

/- A changed accepted producer value is consumed by the downstream expression. -/
example : valueOf ((cascade (.filled storedOld) (.filled storedOldX)).evaluate
    (context (.parsed (.str "ABC")) (.parsed (.str "OLD")))) =
  some (expected (.accepted storedAbc) (some (.value storedAbc))
    (.accepted storedAbcX) (some (.value storedAbcX))) := by
  native_decide

/- An unchanged producer emits no delta, but its accepted outcome still feeds the consumer. -/
example : valueOf ((cascade (.filled storedAbc) (.filled storedOldX)).evaluate
    (context (.parsed (.str "ABC")) (.parsed (.str "ABC")))) =
  some (expected (.accepted storedAbc) none
    (.accepted storedAbcX) (some (.value storedAbcX))) := by
  native_decide

/- A missing producer input clears stale intermediate state before the consumer reads it. -/
example : valueOf ((cascade (.filled storedOld) (.filled storedOldX)).evaluate
    (context .empty (.parsed (.str "OLD")))) =
  some (expected .noValue (some .cleared)
    (.accepted storedDashX) (some (.value storedDashX))) := by
  native_decide

/- A silent no-value producer still supplies the clean missing dependency read; absence of a delta is not absence of an outcome. -/
example : valueOf ((cascade .empty (.filled storedOldX)).evaluate
    (context .empty .empty)) =
  some (expected .noValue none
    (.accepted storedDashX) (some (.value storedDashX))) := by
  native_decide

/- A rejected attempted producer value becomes dependency poison. The consumer cannot read either the attempted value or stale state. -/
example : valueOf ((cascade (.filled storedOld) (.filled storedOldX)).evaluate
    (context (.parsed (.str "ABCD")) (.parsed (.str "OLD")))) =
  some (expected (.errored storedAbcd .tooLong)
    (some (.errored storedAbcd .tooLong))
    (.poison .declaredConstraint) (some .cleared)) := by
  native_decide

/- Validation-scoped requiredness cannot be manufactured as a computation dependency poison. -/
example : errorOf ((context .empty .empty).withDependencyOutcome midId
    (.poison .required)) = some .validationScopedRequired := by
  decide

end A12Kernel.Conformance.StringCascade
