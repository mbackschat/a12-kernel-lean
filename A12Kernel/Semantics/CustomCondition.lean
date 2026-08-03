import A12Kernel.Semantics.MessagePointer

/-! # A12Kernel.Semantics.CustomCondition — resolved callback leaf

This capsule implements the successful reached-leaf boundary of [`spec/11-messages-and-custom.md` §4](../../spec/11-messages-and-custom.md#4-custom-conditions). A preceding integration layer has resolved a registered callback and ordinary validation orchestration has decided to reach it. The callback receives an effective data view, full-versus-partial relevance, the complete formal-invalid-address payload, and the current error pointer. The evaluator does not inspect those opaque channels or pre-suppress the callback because an address is formally invalid.

The oracle is deliberately pure and total. Missing registration, host exceptions, effects, invocation count and order, concrete Java/Node data APIs, relevance construction, message-pointer construction, message emission, and surrounding row/connective evaluation remain outside this boundary. The data, relevance, and formal-invalid payloads remain abstract carriers; the error pointer uses the shared normalized message domain because that distinction is fixed by A12.
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

/-- Evaluate a custom-condition leaf after orchestration has reached it. Callback truth is always VALUE-typed; callback false is the resolved non-firing result. -/
def evalReachedCustomCondition
    (oracle :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses → Bool)
    (invocation :
      CustomConditionInvocation
        DataView RelevantEntities FormalInvalidAddresses) :
    Verdict :=
  if oracle invocation then .fired .value else .notFired

/-- A custom leaf can be reached on an empty row. Surrounding `And`/`Or` structure and whole-rule gating decide whether it actually is reached. -/
def customConditionCanFireOnEmpty : Bool :=
  true

end A12Kernel
