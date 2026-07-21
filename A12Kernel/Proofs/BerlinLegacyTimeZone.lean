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

end A12Kernel
