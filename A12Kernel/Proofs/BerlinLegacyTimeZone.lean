import A12Kernel.Proofs.DateTime
import A12Kernel.Semantics.BerlinLegacyTimeZone

/-! # Versioned Europe/Berlin resolver laws

The non-law beside these laws: resolution is not injective under kernel 31.1.1. A spring-forward gap label resolves one gap later, to the instant of the label after the gap, so two labels share an instant; the conformance module witnesses that pair. Injectivity survives on the labels the zone attains, those with a valid offset.
-/

namespace A12Kernel

/-- A valid offset is the offset actually in force at the instant it names. This is the whole content of the validity filter, isolated so a consumer never unfolds the candidate list. -/
theorem berlin_validOffset_in_force
    {wallMillis offsetSeconds : Int}
    (valid : offsetSeconds ∈ EuropeBerlinLegacyProfile.validOffsets wallMillis) :
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (EuropeBerlinLegacyProfile.candidateInstant wallMillis offsetSeconds) =
      some offsetSeconds := by
  simp only [EuropeBerlinLegacyProfile.validOffsets, List.mem_filter, beq_iff_eq] at valid
  exact valid.2

/-- A label with exactly one valid offset resolves at it, whatever offset is preferred. -/
theorem berlin_resolve_single
    {wallMillis offsetSeconds : Int} (preferred : Option Int)
    (single : EuropeBerlinLegacyProfile.validOffsets wallMillis = [offsetSeconds]) :
    EuropeBerlinLegacyProfile.resolveWall? wallMillis preferred =
      some (EuropeBerlinLegacyProfile.candidateInstant wallMillis offsetSeconds) := by
  unfold EuropeBerlinLegacyProfile.resolveWall?
  rw [single]

/-- A preferred offset that is valid for the label decides its resolution: in an overlap this is how a shift keeps its source's offset. -/
theorem berlin_resolve_preferred_valid
    {wallMillis offsetSeconds : Int}
    (valid : offsetSeconds ∈ EuropeBerlinLegacyProfile.validOffsets wallMillis) :
    EuropeBerlinLegacyProfile.resolveWall? wallMillis (some offsetSeconds) =
      some (EuropeBerlinLegacyProfile.candidateInstant wallMillis offsetSeconds) := by
  unfold EuropeBerlinLegacyProfile.resolveWall?
  rcases offsets : EuropeBerlinLegacyProfile.validOffsets wallMillis with
    _ | ⟨first, _ | ⟨second, rest⟩⟩
  · rw [offsets] at valid
    exact absurd valid List.not_mem_nil
  · rw [offsets, List.mem_singleton] at valid
    subst valid
    rfl
  · rw [offsets] at valid
    have contains : (first :: second :: rest).contains offsetSeconds = true :=
      List.contains_iff_mem.mpr valid
    simp only [contains, ite_true]

/-- Outside a gap, resolution lands at one of the label's valid offsets, whatever offset is preferred. -/
theorem berlin_resolveWall_lands_valid
    {wallMillis : Int} {preferred : Option Int} {instant : Instant}
    (attained : EuropeBerlinLegacyProfile.validOffsets wallMillis ≠ [])
    (resolved : EuropeBerlinLegacyProfile.resolveWall? wallMillis preferred = some instant) :
    ∃ offsetSeconds ∈ EuropeBerlinLegacyProfile.validOffsets wallMillis,
      EuropeBerlinLegacyProfile.candidateInstant wallMillis offsetSeconds = instant := by
  unfold EuropeBerlinLegacyProfile.resolveWall? at resolved
  rcases offsets : EuropeBerlinLegacyProfile.validOffsets wallMillis with
    _ | ⟨first, _ | ⟨second, rest⟩⟩
  · exact absurd offsets attained
  · rw [offsets] at resolved
    exact ⟨first, List.mem_singleton_self _, Option.some.inj resolved⟩
  · rw [offsets] at resolved
    have fromMax : ∀ offsetSeconds,
        (first :: second :: rest).max? = some offsetSeconds →
        EuropeBerlinLegacyProfile.candidateInstant wallMillis offsetSeconds = instant →
        ∃ selected ∈ first :: second :: rest,
          EuropeBerlinLegacyProfile.candidateInstant wallMillis selected = instant :=
      fun offsetSeconds isMax landed => ⟨offsetSeconds, List.max?_mem isMax, landed⟩
    cases preferred with
    | none =>
        simp only [Option.map_eq_some_iff] at resolved
        obtain ⟨offsetSeconds, isMax, landed⟩ := resolved
        exact fromMax offsetSeconds isMax landed
    | some preferredOffset =>
        by_cases valid : (first :: second :: rest).contains preferredOffset = true
        · simp only [valid, ite_true, Option.some.injEq] at resolved
          exact ⟨preferredOffset, List.contains_iff_mem.mp valid, resolved⟩
        · simp only [valid, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at resolved
          obtain ⟨offsetSeconds, isMax, landed⟩ := resolved
          exact fromMax offsetSeconds isMax landed

/-- Two attained wall clocks that resolve to one instant are equal: the instant fixes the offset in force, and with it the wall clock. A gap label is excluded because it lands at the instant of a different label. -/
theorem berlin_resolveWall_injective_attained
    {left right : Int} {leftPreferred rightPreferred : Option Int} {instant : Instant}
    (leftAttained : EuropeBerlinLegacyProfile.validOffsets left ≠ [])
    (rightAttained : EuropeBerlinLegacyProfile.validOffsets right ≠ [])
    (leftResolved : EuropeBerlinLegacyProfile.resolveWall? left leftPreferred = some instant)
    (rightResolved : EuropeBerlinLegacyProfile.resolveWall? right rightPreferred = some instant) :
    left = right := by
  obtain ⟨leftOffset, leftValid, leftLanded⟩ :=
    berlin_resolveWall_lands_valid leftAttained leftResolved
  obtain ⟨rightOffset, rightValid, rightLanded⟩ :=
    berlin_resolveWall_lands_valid rightAttained rightResolved
  have leftForce := berlin_validOffset_in_force leftValid
  have rightForce := berlin_validOffset_in_force rightValid
  rw [leftLanded] at leftForce
  rw [rightLanded, leftForce, Option.some.injEq] at rightForce
  subst rightForce
  have candidates := leftLanded.trans rightLanded.symm
  simp only [EuropeBerlinLegacyProfile.candidateInstant, Instant.mk.injEq] at candidates
  omega

end A12Kernel
