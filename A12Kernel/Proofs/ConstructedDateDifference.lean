import A12Kernel.Semantics.DateConstructionNumeric

/-! # Constructed-Date difference laws

The reason-bearing combination of two constructed Dates is owned by `DateConstructionResult.differenceWith?`; its laws hold for every concrete counter, so they are stated once here and not per calendar profile.
-/

namespace A12Kernel

/-- A formally unavailable first operand dominates every constructed-Date difference branch. -/
theorem constructedDateDifference_unavailable_left
    (between : DateParts → DateParts → Option Int) (right : DateConstructionResult) :
    DateConstructionResult.unknown.differenceWith? between right =
      some .unavailable := by
  cases right <;> rfl

/-- Incomplete and unreal operands both produce zero but remain distinguishable by missing provenance. -/
theorem constructedDateDifference_nonvalue_provenance
    (between : DateParts → DateParts → Option Int) (right : DateConstructionResult) :
    DateConstructionResult.incomplete.differenceWith? between right =
        (if right = .unknown then some .unavailable else some (.value 0 true)) ∧
      DateConstructionResult.unreal.differenceWith? between right =
        (if right = .unknown then some .unavailable else
          if right = .incomplete then some (.value 0 true)
          else some (.value 0 false)) := by
  cases right <;> simp [DateConstructionResult.differenceWith?]

end A12Kernel
