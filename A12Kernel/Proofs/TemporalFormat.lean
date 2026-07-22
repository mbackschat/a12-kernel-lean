import A12Kernel.Semantics.TemporalFormat

/-! # Temporal format-admission laws -/

namespace A12Kernel

/-- Direct format admission is independent of operand position. -/
theorem temporalComparison_admitsFormats_symmetric (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (left right : TemporalComponents) :
    op.admitsFormats hasBaseYear left right =
      op.admitsFormats hasBaseYear right left := by
  simp [TemporalComparisonOp.admitsFormats, Bool.beq_comm]

/-- Exact aggregate component compatibility is sufficient for every direct comparison operator. -/
theorem temporalAggregateFormatsCompatible_implies_comparison
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (left right : TemporalComponents)
    (compatible : temporalAggregateFormatsCompatible hasBaseYear left right = true) :
    op.admitsFormats hasBaseYear left right = true := by
  simp [temporalAggregateFormatsCompatible] at compatible
  simp [TemporalComparisonOp.admitsFormats, compatible]

/-- Equality admission is stricter than directional admission only by its time-presence check. -/
theorem temporalEqualFormats_implies_beforeFormats
    (hasBaseYear : Bool) (left right : TemporalComponents)
    (compatible : TemporalComparisonOp.equal.admitsFormats hasBaseYear left right = true) :
    TemporalComparisonOp.before.admitsFormats hasBaseYear left right = true := by
  simp [TemporalComparisonOp.admitsFormats,
    TemporalComparisonOp.requiresSameTimePresence] at compatible ⊢
  exact compatible.1

/-- Every statically admitted `Now` comparison has the additional time-bearing operand required by generated code. -/
theorem temporalComparison_admitsNow_hasTime
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (other : TemporalComponents)
    (admitted : op.admitsNow hasBaseYear other = true) :
    other.hasTime = true := by
  simp [TemporalComparisonOp.admitsNow] at admitted
  exact admitted.left

/-- `Now` admission never bypasses the ordinary direct-comparison format gate. -/
theorem temporalComparison_admitsNow_admitsFormats
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (other : TemporalComponents)
    (admitted : op.admitsNow hasBaseYear other = true) :
    op.admitsFormats hasBaseYear other TemporalComponents.now = true := by
  simp [TemporalComparisonOp.admitsNow] at admitted
  exact admitted.right

end A12Kernel
