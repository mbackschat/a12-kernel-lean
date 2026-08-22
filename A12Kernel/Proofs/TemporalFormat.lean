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

/-- Every admitted temporal target retains a nonempty exact format source. -/
theorem temporalTargetPolicy_valid_format_nonempty
    (policy : TemporalTargetPolicy)
    (kind : TemporalKind) (components : TemporalComponents)
    (valid : policy.errorFor? kind components = none) :
    policy.format.isEmpty = false := by
  cases h : policy.format.isEmpty <;>
    simp_all [TemporalTargetPolicy.errorFor?]

/-- Every admitted DateRange declaration retains a nonempty exact format, and the legal empty separator belongs to the month-only format alone. The former conjunct requiring a nonempty separator was refuted by the Kernel-measured allowlist. -/
theorem dateRangeDeclarationPolicy_valid_sources
    (policy : DateRangeDeclarationPolicy)
    (valid : policy.error? = none) :
    policy.format.isEmpty = false ∧
      (policy.separator.isEmpty = true → policy.format = "MM") := by
  have hAdmitted : policy.admitted = true := by
    cases h : policy.admitted <;> simp_all [DateRangeDeclarationPolicy.error?]
  unfold DateRangeDeclarationPolicy.admitted at hAdmitted
  split at hAdmitted <;> simp_all

/-- A non-Date target can retain neither partial-date admission nor the Date-only pre-1900 check. -/
theorem temporalTargetPolicy_valid_nonDate
    (policy : TemporalTargetPolicy)
    (kind : TemporalKind) (components : TemporalComponents)
    (notDate : kind ≠ .date)
    (valid : policy.errorFor? kind components = none) :
    policy.partialMode = .full ∧ policy.youngerThan1900Check = false := by
  cases kind <;> simp_all
  all_goals
    cases hPartialMode : policy.partialMode <;>
      cases hAdditional : policy.youngerThan1900Check <;>
      by_cases hFormat : policy.format = "" <;>
      simp_all [TemporalTargetPolicy.errorFor?]

/-- A non-full partial-date mode certifies a full Date component set. -/
theorem temporalTargetPolicy_valid_partial
    (policy : TemporalTargetPolicy)
    (kind : TemporalKind) (components : TemporalComponents)
    (notFull : policy.partialMode ≠ .full)
    (valid : policy.errorFor? kind components = none) :
    kind = .date ∧ components = TemporalComponents.fullDate := by
  cases kind with
  | date =>
      by_cases hFormat : policy.format = ""
      · simp [TemporalTargetPolicy.errorFor?, hFormat] at valid
      by_cases hComponents : components = TemporalComponents.fullDate
      · exact ⟨rfl, hComponents⟩
      · simp [TemporalTargetPolicy.errorFor?, hFormat, notFull,
          hComponents] at valid
  | time =>
      by_cases hFormat : policy.format = "" <;>
        simp_all [TemporalTargetPolicy.errorFor?]
  | dateTime =>
      by_cases hFormat : policy.format = "" <;>
        simp_all [TemporalTargetPolicy.errorFor?]

end A12Kernel
