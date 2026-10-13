import A12Kernel.Elaboration.DeclarationReport

/-! # Declaration-report withholding laws

The report's two regimes, stated over every member verdict: a refusal leaves the other slots and the
prefixed presence classes beside it and nothing of the error-text checker, and a sound declaration
reports every member. A failed target is the refusal whatever the DSL members drew.
-/

namespace A12Kernel.DeclarationVerdicts

theorem report_of_refusal (verdicts : DeclarationVerdicts) (refused : verdicts.refusal ≠ []) :
    verdicts.report = verdicts.slots ++ verdicts.presence.prefixed ++ verdicts.refusal := by
  simp [report, refused]

theorem report_of_sound (verdicts : DeclarationVerdicts) (sound : verdicts.refusal = []) :
    verdicts.report = verdicts.slots ++ verdicts.presence.prefixed ++ verdicts.presence.unprefixed ++
      verdicts.errorText := by
  simp [report, sound]

theorem refusal_of_target (verdicts : DeclarationVerdicts) (failed : verdicts.target ≠ []) :
    verdicts.refusal = verdicts.target := by
  simp [refusal, failed]

end A12Kernel.DeclarationVerdicts
