import A12Kernel.Elaboration.Flat.Types

/-! # Field-identifier list laws -/

namespace A12Kernel

theorem fieldId_firstDuplicate_none_iff_nodup (fields : List FieldId) :
    FieldId.firstDuplicate? fields = none ↔ fields.Nodup := by
  induction fields with
  | nil => simp [FieldId.firstDuplicate?]
  | cons field remaining inductionHypothesis =>
      by_cases member : field ∈ remaining <;>
        simp [FieldId.firstDuplicate?, member, inductionHypothesis]

end A12Kernel
