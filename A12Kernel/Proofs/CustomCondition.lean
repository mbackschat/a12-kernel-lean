import A12Kernel.Semantics.CustomCondition

/-! # A12Kernel.Proofs.CustomCondition — resolved callback laws

These laws characterize the pure successful-callback boundary. They prove exact invocation transparency and the two possible verdicts, while the concrete witnesses show why purity alone supplies neither document locality nor monotonicity in the formal-invalid payload. They do not cover callback registration, host failure, effects, call count, invocation construction, or surrounding rule evaluation.
-/

namespace A12Kernel

universe u v w

/-- The callback fires as VALUE exactly when the oracle returns true for the supplied invocation. Because the invocation is passed literally, none of its four opaque channels is interpreted or pre-gated here. -/
theorem evalReachedCustomCondition_fired_value_iff
    (oracle :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses → Bool)
    (invocation :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses) :
    evalReachedCustomCondition oracle invocation = .fired .value ↔
      oracle invocation = true := by
  simp [evalReachedCustomCondition, customConditionVerdict]

/-- The callback is non-firing exactly when the oracle returns false. -/
theorem evalReachedCustomCondition_notFired_iff
    (oracle :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses → Bool)
    (invocation :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses) :
    evalReachedCustomCondition oracle invocation = .notFired ↔
      oracle invocation = false := by
  simp [evalReachedCustomCondition, customConditionVerdict]

/-- A successfully evaluated custom callback never produces evaluator UNKNOWN. -/
theorem evalReachedCustomCondition_ne_unknown
    (oracle :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses → Bool)
    (invocation :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses) :
    evalReachedCustomCondition oracle invocation ≠ .unknown := by
  cases h : oracle invocation <;>
    simp [evalReachedCustomCondition, customConditionVerdict, h]

/-- A successfully evaluated custom callback never fires with omission polarity. -/
theorem evalReachedCustomCondition_ne_omission
    (oracle :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses → Bool)
    (invocation :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses) :
    evalReachedCustomCondition oracle invocation ≠ .fired .omission := by
  cases h : oracle invocation <;>
    simp [evalReachedCustomCondition, customConditionVerdict, h]

/-- Structural empty-row eligibility is unconditional at the custom leaf. -/
theorem customConditionCanFireOnEmpty_eq_true :
    customConditionCanFireOnEmpty = true := by
  rfl

private def dataInvocation (data : Bool) :
    CustomConditionInvocation Bool Unit Unit :=
  {
    data
    relevance := .all
    formallyIncorrect := ()
    errorPointer := MessagePointer.ofCellAddr { field := 1, path := [] }
  }

private def readsData
    (invocation : CustomConditionInvocation Bool Unit Unit) : Bool :=
  invocation.data

/-- A pure callback may observe arbitrary data-view distinctions, so purity alone does not imply locality to declared rule references. -/
theorem customCondition_purity_does_not_imply_data_locality :
    evalReachedCustomCondition readsData (dataInvocation true) =
        .fired .value ∧
      evalReachedCustomCondition readsData (dataInvocation false) =
        .notFired := by
  decide

private def formalInvocation (formallyIncorrect : Bool) :
    CustomConditionInvocation Unit Unit Bool :=
  {
    data := ()
    relevance := .all
    formallyIncorrect
    errorPointer := MessagePointer.ofCellAddr { field := 1, path := [] }
  }

private def readsFormalInvalid
    (invocation : CustomConditionInvocation Unit Unit Bool) : Bool :=
  invocation.formallyIncorrect

private def reversesFormalInvalid
    (invocation : CustomConditionInvocation Unit Unit Bool) : Bool :=
  !invocation.formallyIncorrect

/-- Pure callbacks can react to the formal-invalid payload in either direction; no invalidity monotonicity follows without a separate oracle contract. -/
theorem customCondition_purity_does_not_imply_formal_monotonicity :
    evalReachedCustomCondition readsFormalInvalid (formalInvocation false) =
        .notFired ∧
      evalReachedCustomCondition readsFormalInvalid (formalInvocation true) =
        .fired .value ∧
      evalReachedCustomCondition reversesFormalInvalid (formalInvocation false) =
        .fired .value ∧
      evalReachedCustomCondition reversesFormalInvalid (formalInvocation true) =
        .notFired := by
  decide

/-- Per-call configuration replaces the fallback chain even when the selected factory declines. -/
theorem customCondition_configured_factory_wins
    (factory : String → Option (Invocation → Bool)) (fallback : List (String → Option (Invocation → Bool)))
    (name : String) :
    (CustomConditionRegistry.resolve { configured := some factory, fallback } name) = factory name := by
  rfl

/-- Resolution adds no filtering or projection to the callback's invocation payload. -/
theorem customCondition_invoke_resolved
    (registry : CustomConditionRegistry (CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses))
    (name : String) (invocation : CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses)
    (callback : CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses → Bool)
    (resolved : registry.resolve name = some callback) :
    registry.invoke name invocation = .ok (evalReachedCustomCondition callback invocation) := by
  simp [CustomConditionRegistry.invoke, CustomConditionRegistry.evaluate, resolved, Except.map]
  rfl

end A12Kernel
