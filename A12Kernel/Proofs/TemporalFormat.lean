import A12Kernel.Semantics.TemporalFormat

/-! # Temporal format-admission laws -/

namespace A12Kernel

/-- Direct format admission is independent of operand position. -/
theorem temporalComparison_admitsFormats_symmetric (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (left right : TemporalComponents) :
    op.admitsFormats hasBaseYear left right =
      op.admitsFormats hasBaseYear right left := by
  simp [TemporalComparisonOp.admitsFormats, Bool.beq_comm]

/-- Base Year may equalize year presence, but direct comparison admission always preserves the operands' original date-versus-time class. -/
theorem temporalComparison_admitsFormats_sameDateClass
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (left right : TemporalComponents)
    (admitted : op.admitsFormats hasBaseYear left right = true) :
    left.hasDate = right.hasDate := by
  simp [TemporalComparisonOp.admitsFormats] at admitted
  exact admitted.1.2

/-- Exact aggregate component compatibility is sufficient for every direct comparison operator. -/
theorem temporalAggregateFormatsCompatible_implies_comparison
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (left right : TemporalComponents)
    (compatible : temporalAggregateFormatsCompatible hasBaseYear left right = true) :
    op.admitsFormats hasBaseYear left right = true := by
  simp [temporalAggregateFormatsCompatible] at compatible
  have timeEq : left.hasTime = right.hasTime := by
    have componentTimeEq := congrArg TemporalComponents.hasTime compatible.right
    cases hasBaseYear <;>
      simpa [TemporalComponents.withBaseYear, TemporalComponents.hasTime] using componentTimeEq
  simp [TemporalComparisonOp.admitsFormats, compatible, timeEq]

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

/-- `Today` admission is exactly ordinary date-shaped direct-comparison admission. -/
theorem temporalComparison_admitsToday_admitsFormats
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (other : TemporalComponents)
    (admitted : op.admitsToday hasBaseYear other = true) :
    op.admitsFormats hasBaseYear other TemporalComponents.today = true := by
  exact admitted

/-- Equality with `Today` excludes a time-bearing counterpart; directional comparison retains the kernel's coarser date-class gate. -/
theorem temporalEqual_admitsToday_hasNoTime
    (hasBaseYear : Bool) (other : TemporalComponents)
    (admitted : TemporalComparisonOp.equal.admitsToday hasBaseYear other = true) :
    other.hasTime = false := by
  cases hasBaseYear <;>
    simp_all [TemporalComparisonOp.admitsToday, TemporalComparisonOp.admitsFormats,
      TemporalComparisonOp.requiresSameTimePresence, TemporalComponents.today,
      TemporalComponents.fullDate, TemporalComponents.withBaseYear,
      TemporalComponents.hasTime]

/-- Base Year cannot become comparable to a time-only operand merely because year supplementation runs later. -/
theorem temporalComparison_admitsBaseYear_hasDate
    (op : TemporalComparisonOp) (other : TemporalComponents)
    (admitted : op.admitsBaseYear other = true) :
    other.hasDate = true := by
  simp [TemporalComparisonOp.admitsBaseYear] at admitted
  exact admitted.left

end A12Kernel
