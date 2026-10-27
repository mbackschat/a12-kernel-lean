import A12Kernel.Semantics.MessagePointer

/-! # A12Kernel.Semantics.CustomCondition — resolved callback leaf

This capsule implements the successful reached-leaf boundary of [`spec/11-messages-and-custom.md` §14](../../spec/11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch). A preceding integration layer has resolved a registered callback and ordinary validation orchestration has decided to reach it. The callback receives an effective data view, full-versus-partial relevance, the complete formal-invalid-address payload, and the current error pointer. The evaluator does not inspect those opaque channels or pre-suppress the callback because an address is formally invalid.

The oracle is deliberately pure and total. The registry below models per-call factory precedence, ordered fallback lookup and reached missing-registration failure. Host exceptions, mutable callback effects and concrete Java/Node APIs remain outside this account; the shared validation tree and checked rule own call order, invocation construction and message emission. The data, relevance, and formal-invalid payloads remain abstract carriers; the error pointer uses the shared normalized message domain because that distinction is fixed by A12.
-/

namespace A12Kernel

universe u v w

/-- Full validation is observably distinct from partial validation with an empty relevant-entity container. -/
inductive CustomConditionRelevance (RelevantEntities : Type v) where
  | all
  | partialEntities (entities : RelevantEntities)

/-- The four semantic channels passed unchanged to one successfully resolved custom-condition callback. -/
structure CustomConditionInvocation
    (DataView : Type u)
    (RelevantEntities : Type v)
    (FormalInvalidAddresses : Type w) where
  data : DataView
  relevance : CustomConditionRelevance RelevantEntities
  formallyIncorrect : FormalInvalidAddresses
  errorPointer : MessagePointer

def customConditionVerdict (holds : Bool) : Verdict :=
  if holds then .fired .value else .notFired

/-- Evaluate a custom-condition leaf after orchestration has reached it. Callback truth is always VALUE-typed; callback false is the resolved non-firing result. -/
def evalReachedCustomCondition
    (oracle :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses → Bool)
    (invocation :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses) :
    Verdict :=
  customConditionVerdict (oracle invocation)

/-- A custom leaf can be reached on an empty row. Surrounding `And`/`Or` structure and whole-rule gating decide whether it actually is reached. -/
def customConditionCanFireOnEmpty : Bool :=
  true

/-- Pure successful factories supplied by the host. A configured per-call factory replaces the
fallback chain, even when it has no match (ValidationCache.getCustomCondition, kernel 30.8.1). -/
structure CustomConditionRegistry (Invocation : Type u) where
  configured : Option (String → Option (Invocation → Bool)) := none
  fallback : List (String → Option (Invocation → Bool)) := []

/-- Missing registration is observable only when the condition is reached; callbacks and factory
exceptions remain explicit host failures outside the pure successful-factory account (spec/11 §14). -/
inductive CustomConditionLookupError where
  | unavailableInvocation
  | missingRegistration (name : String)
  /-- A rule reporting on a group: every reached call fails without invoking a callback, whatever the
  name or its registered answer. The measured outcomes do not separate a failure before the lookup
  from one after it, so the peer's account of the cause (KF615) is not adopted
  ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-k22-group-target-custom-abort)). -/
  | groupErrorEntity
  deriving Repr, DecidableEq

namespace CustomConditionRegistry

/-- Ordered factories choose the first match; later registrations cannot override it
(CustomConditionService.getCustomCondition, kernel 30.8.1). -/
def resolve (registry : CustomConditionRegistry Invocation) (name : String) :
    Option (Invocation → Bool) :=
  match registry.configured with
  | some factory => factory name
  | none => registry.fallback.findSome? (fun factory => factory name)

/-- Resolve only a reached callback and preserve the successful leaf's exact invocation channels. -/
def evaluate (registry : CustomConditionRegistry
    (CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses))
    (name : String) (invocation : CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses) :
    Except CustomConditionLookupError Bool := do
  let some callback := registry.resolve name | throw (.missingRegistration name)
  pure (callback invocation)

def invoke (registry : CustomConditionRegistry
    (CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses))
    (name : String) (invocation : CustomConditionInvocation DataView RelevantEntities FormalInvalidAddresses) :
    Except CustomConditionLookupError Verdict :=
  (registry.evaluate name invocation).map customConditionVerdict

end CustomConditionRegistry

end A12Kernel
