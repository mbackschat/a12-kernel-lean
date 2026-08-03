import A12Kernel.Semantics.ComputationMessage
import A12Kernel.Proofs.MessagePointer

/-! # Computation-message pointer and partition laws -/

namespace A12Kernel

/-- A message enters the computed-instance side exactly when it belongs to the input stream and its complete pointer occurs in the computed-instance set. -/
theorem partitionComputationMessages_atComputedInstances_iff
    (computedInstances : List MessagePointer)
    (messages : List (ComputationFormalMessage Payload))
    (message : ComputationFormalMessage Payload) :
    message ∈
        (partitionComputationMessages computedInstances messages
          ).atComputedInstances ↔
      message ∈ messages ∧ message.pointer ∈ computedInstances := by
  simp [partitionComputationMessages]

/-- A message enters the residual side exactly when it belongs to the input stream and its complete pointer is absent from the computed-instance set. -/
theorem partitionComputationMessages_residual_iff
    (computedInstances : List MessagePointer)
    (messages : List (ComputationFormalMessage Payload))
    (message : ComputationFormalMessage Payload) :
    message ∈
        (partitionComputationMessages computedInstances messages).residual ↔
      message ∈ messages ∧ message.pointer ∉ computedInstances := by
  simp [partitionComputationMessages]

/-- Every input message belongs to exactly one side at the membership level. -/
theorem partitionComputationMessages_complete
    (computedInstances : List MessagePointer)
    (messages : List (ComputationFormalMessage Payload))
    (message : ComputationFormalMessage Payload) :
    (message ∈
        (partitionComputationMessages computedInstances messages
          ).atComputedInstances ∨
      message ∈
        (partitionComputationMessages computedInstances messages).residual) ↔
      message ∈ messages := by
  rw [partitionComputationMessages_atComputedInstances_iff,
    partitionComputationMessages_residual_iff]
  constructor
  · intro side
    exact side.elim (·.1) (·.1)
  · intro member
    by_cases matched : message.pointer ∈ computedInstances
    · exact .inl ⟨member, matched⟩
    · exact .inr ⟨member, matched⟩

end A12Kernel
