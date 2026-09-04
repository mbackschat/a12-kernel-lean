import A12Kernel.Semantics.TemporalFormat

/-! # Temporal format-admission laws -/

namespace A12Kernel

/-- Direct format admission is independent of operand position. -/
theorem temporalComparison_admitsFormats_symmetric (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (left right : TemporalComponents) :
    op.admitsFormats hasBaseYear left right =
      op.admitsFormats hasBaseYear right left := by
  simp [TemporalComparisonOp.admitsFormats, temporalYearPresenceAgrees, Bool.beq_comm]

/-- Base Year may equalize year presence, but direct comparison admission always preserves the operands' original date-versus-time class. -/
theorem temporalComparison_admitsFormats_sameDateClass
    (op : TemporalComparisonOp) (hasBaseYear : Bool)
    (left right : TemporalComponents)
    (admitted : op.admitsFormats hasBaseYear left right = true) :
    left.hasDate = right.hasDate := by
  simp [TemporalComparisonOp.admitsFormats, temporalYearPresenceAgrees] at admitted
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
  simp [TemporalComparisonOp.admitsFormats, temporalYearPresenceAgrees, compatible, timeEq]

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
      TemporalComponents.fullDate, TemporalComponents.hasTime]

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

/-- A temporal operation's operand fault is independent of authored operand position, on both
grounds. Measured on three pairs rather than asserted from the definition's shape: each ground
reports the identical Kernel code in either order, and the admitted row survives reversal. -/
theorem temporalOperation_operandFault_symmetric (unit : TemporalOperationUnit)
    (hasBaseYear : Bool) (left right : TemporalComponents) :
    unit.operandFault? hasBaseYear left right =
      unit.operandFault? hasBaseYear right left := by
  unfold TemporalOperationUnit.operandFault? temporalYearPresenceAgrees
  cases hLeft : unit.operandResolves hasBaseYear left
  case false => simp
  case true =>
    cases hRight : unit.operandResolves hasBaseYear right
    case false => simp
    case true =>
      cases hLeftYear : (left.withBaseYear hasBaseYear).year <;>
        cases hRightYear : (right.withBaseYear hasBaseYear).year <;>
        simp_all

/-- Position independence carries to admission itself. -/
theorem temporalOperation_admitsOperands_symmetric (unit : TemporalOperationUnit)
    (hasBaseYear : Bool) (left right : TemporalComponents) :
    unit.admitsOperands hasBaseYear left right =
      unit.admitsOperands hasBaseYear right left := by
  simp [TemporalOperationUnit.admitsOperands,
    temporalOperation_operandFault_symmetric unit hasBaseYear left right]

/-- `withBaseYear` only ever sets `year`, so a resolvable operand stays resolvable once a Base
Year is declared, and a `years` operand becomes resolvable. -/
private theorem temporalOperation_operandResolves_baseYear_monotone
    (unit : TemporalOperationUnit) (components : TemporalComponents)
    (resolved : unit.operandResolves false components = true) :
    unit.operandResolves true components = true := by
  cases unit <;>
    simp_all [TemporalOperationUnit.operandResolves,
      TemporalOperationUnit.requiredComponent, TemporalComponents.withBaseYear]

/-- **Declaring a Base Year is purely permissive on this gate: it never refuses a pair the
unconfigured model admits.** This is the property a consumer needs before adding one to an
existing model, and it is not obvious from the two grounds — supplementation feeds *both* of
them, so a naive reading fears it could equalize the years while disturbing granularity. It
cannot: `withBaseYear` only ever sets `year`, so each operand's required component is monotone
and the year comparison becomes `true == true`. The converse fails, which is the whole point of
the Base Year here — a yearless pair is refused in `years` without one and admitted with one. -/
theorem temporalOperation_admitsOperands_baseYear_monotone
    (unit : TemporalOperationUnit) (left right : TemporalComponents)
    (admitted : unit.admitsOperands false left right = true) :
    unit.admitsOperands true left right = true := by
  simp only [TemporalOperationUnit.admitsOperands, Option.isNone_iff_eq_none,
    TemporalOperationUnit.operandFault?, temporalYearPresenceAgrees] at admitted ⊢
  by_cases hLeft : unit.operandResolves false left = true
  · by_cases hRight : unit.operandResolves false right = true
    · have monoLeft := temporalOperation_operandResolves_baseYear_monotone unit left hLeft
      have monoRight := temporalOperation_operandResolves_baseYear_monotone unit right hRight
      simp [monoLeft, monoRight, TemporalComponents.withBaseYear]
    · simp [hRight] at admitted
  · simp [hLeft] at admitted

/-- **A declared Base Year makes year agreement vacuous.** One line, stated as a theorem because
this is the qualification both this project's and a12-dmkits' prose asserted unqualified before
either measured the configured quadrant: with a Base Year in scope no operand pair can disagree
about the year, so neither gate below can refuse on that ground. -/
theorem temporalYearPresenceAgrees_baseYear (left right : TemporalComponents) :
    temporalYearPresenceAgrees true left right = true := by
  simp [temporalYearPresenceAgrees, TemporalComponents.withBaseYear]

/-- **The direct-comparison gate and the operation operand gate read the same year rule**, so a
year disagreement refuses on both carriers and the two cannot silently diverge. This is the payoff
of factoring the predicate rather than writing it twice: the gates differ in every other respect
— granularity, date class, time presence, and their refusal codes — and agree on exactly this. -/
theorem temporalYearPresence_shared_by_both_gates (op : TemporalComparisonOp)
    (unit : TemporalOperationUnit) (hasBaseYear : Bool)
    (left right : TemporalComponents)
    (disagree : temporalYearPresenceAgrees hasBaseYear left right = false) :
    op.admitsFormats hasBaseYear left right = false ∧
      unit.admitsOperands hasBaseYear left right = false := by
  refine ⟨by simp [TemporalComparisonOp.admitsFormats, disagree], ?_⟩
  simp only [TemporalOperationUnit.admitsOperands, TemporalOperationUnit.operandFault?,
    disagree]
  cases hResolves :
      (unit.operandResolves hasBaseYear left && unit.operandResolves hasBaseYear right) <;>
    simp_all

end A12Kernel
