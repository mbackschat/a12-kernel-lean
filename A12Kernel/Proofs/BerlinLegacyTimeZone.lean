import A12Kernel.Proofs.DateTime
import A12Kernel.Semantics.BerlinLegacyTimeZone

/-! # Versioned Europe/Berlin resolver laws -/

namespace A12Kernel

/-- Whenever standard offset is valid for a fresh label, it wins over every larger overlap candidate. -/
theorem berlinLegacy_resolve_prefers_3600
    (dateTime : LocalDateTime)
    (standardValid :
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (EuropeBerlinLegacyProfile.candidateInstant dateTime 3600) =
        some 3600) :
    EuropeBerlinLegacyProfile.resolveLocal? dateTime =
      some (EuropeBerlinLegacyProfile.candidateInstant dateTime 3600) := by
  simp [EuropeBerlinLegacyProfile.resolveLocal?,
    EuropeBerlinLegacyProfile.selectedOffset?,
    EuropeBerlinLegacyProfile.candidateOffsets,
    standardValid]

/-- Daylight offset wins when standard offset is invalid and both daylight and double-summer candidates are considered. -/
theorem berlinLegacy_resolve_prefers_7200
    (dateTime : LocalDateTime)
    (standardInvalid :
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (EuropeBerlinLegacyProfile.candidateInstant dateTime 3600) ≠
        some 3600)
    (daylightValid :
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (EuropeBerlinLegacyProfile.candidateInstant dateTime 7200) =
        some 7200) :
    EuropeBerlinLegacyProfile.resolveLocal? dateTime =
      some (EuropeBerlinLegacyProfile.candidateInstant dateTime 7200) := by
  simp [EuropeBerlinLegacyProfile.resolveLocal?,
    EuropeBerlinLegacyProfile.selectedOffset?,
    EuropeBerlinLegacyProfile.candidateOffsets,
    standardInvalid, daylightValid]

/-- A resolved fresh label's selected offset is the offset actually in force at the instant it
resolved to. That is the whole content of the candidate search's predicate, isolated here so a
consumer never unfolds the candidate list to use it. -/
theorem berlinLegacy_resolveLocal_offset_in_force
    {dateTime : LocalDateTime} {instant : Instant} {offsetSeconds : Int}
    (selected :
      EuropeBerlinLegacyProfile.selectedOffset? dateTime = some offsetSeconds)
    (resolved :
      EuropeBerlinLegacyProfile.candidateInstant dateTime offsetSeconds =
        instant) :
    EuropeBerlinLegacyProfile.offsetSecondsAt? instant = some offsetSeconds := by
  have predicate := List.find?_some selected
  simp only [beq_iff_eq] at predicate
  exact resolved ▸ predicate

/-- **Fresh-label resolution is injective: two distinct wall labels never resolve to one instant.**

    The reason is the lemma above rather than anything about the transition table — the offset is
    recovered from the *instant*, so both labels are forced to the same offset and then to the same
    UTC coordinate. It therefore survives any change to the pinned history, and it holds for the
    overlap as well: a label inside the fall-back hour resolves to exactly one of its two candidate
    instants, and the other is reachable only by a value that *retains* an instant rather than
    deriving one from a label.

    What it does **not** say is that resolution is total. A spring-forward gap label matches no
    candidate and resolves to `none`, so the injection is partial and a gap label has no instant to
    collide with. -/
theorem berlinLegacy_resolveLocal_injective
    {left right : LocalDateTime} {instant : Instant}
    (leftResolved : EuropeBerlinLegacyProfile.resolveLocal? left = some instant)
    (rightResolved :
      EuropeBerlinLegacyProfile.resolveLocal? right = some instant) :
    left = right := by
  simp only [EuropeBerlinLegacyProfile.resolveLocal?, Option.map_eq_some_iff]
    at leftResolved rightResolved
  obtain ⟨leftOffset, leftSelected, leftInstant⟩ := leftResolved
  obtain ⟨rightOffset, rightSelected, rightInstant⟩ := rightResolved
  have leftForce :=
    berlinLegacy_resolveLocal_offset_in_force leftSelected leftInstant
  have rightForce :=
    berlinLegacy_resolveLocal_offset_in_force rightSelected rightInstant
  have sameOffset : leftOffset = rightOffset := by
    rw [leftForce] at rightForce
    exact Option.some.injEq _ _ ▸ rightForce
  subst sameOffset
  have millis : left.resolveUtc.epochMillis = right.resolveUtc.epochMillis := by
    have candidates := leftInstant.trans rightInstant.symm
    simp only [EuropeBerlinLegacyProfile.candidateInstant, Instant.mk.injEq]
      at candidates
    omega
  exact localDateTime_resolveUtc_injective _ _ (instant_eq_of_epochMillis millis)

end A12Kernel
