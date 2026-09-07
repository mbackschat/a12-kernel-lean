import A12Kernel.Elaboration.DynamicEnumerationLegality

/-! # Dynamic-enumeration legality laws

The derivation's four stages are first-match-wins, and everything a consumer can rely on follows from that one property stated exactly: the reported class is the *first* violated stage condition, so an earlier defect hides every later one and no consumer can read acceptance out of a later stage's silence.
-/

namespace A12Kernel

/-- The value-calculation stage reports only its own stage's classes. This is what the separate
`DynEnumValueCalcRefusal` type buys, and every masking result below rests on it. -/
theorem dynEnumValueCalcRefusal_stage (v : DynEnumValueCalcRefusal) :
    v.toRefusal.stage = .valueCalculation := by
  cases v <;> rfl

/-- The reported class is the first violation in stage order. Stated against `dynEnumViolations`,
which lists every violated condition independently of the pipeline, so this relates two definitions
rather than restating one. -/
theorem dynEnumLegality_eq_first_violation (c : DynEnumCandidate) :
    dynEnumLegality c = (dynEnumViolations c).head? := by
  unfold dynEnumLegality dynEnumViolations
  cases hm : c.hModel <;> cases ht : targetTypeAdmits c.target <;>
    cases hi : c.targetIsIndexField <;> cases hp : c.usesParallelIteration <;>
    cases hr : c.usesRepetitionNotUnique <;> cases hg : c.gateCanonical <;>
    cases hv : c.valueCalculation <;> simp_all

/-- Acceptance is exactly the absence of any violation, so a consumer may decide "is this a dynamic
enumeration?" from either side without the two disagreeing. -/
theorem dynEnumLegality_none_iff (c : DynEnumCandidate) :
    dynEnumLegality c = none ↔ dynEnumViolations c = [] := by
  rw [dynEnumLegality_eq_first_violation]
  cases h : dynEnumViolations c <;> simp

/-- The reported class is the earliest-staged violation, not merely one of them. This is the
precedence a repair tool needs: fixing a later-stage defect can never change an earlier-stage
verdict, so the classes have to be addressed in stage order. -/
theorem dynEnumLegality_stage_minimal (c : DynEnumCandidate) (reported violated : DynEnumRefusal)
    (hReported : dynEnumLegality c = some reported)
    (hViolated : violated ∈ dynEnumViolations c) :
    reported.stage.order ≤ violated.stage.order := by
  unfold dynEnumLegality at hReported
  unfold dynEnumViolations at hViolated
  cases hm : c.hModel <;> cases ht : targetTypeAdmits c.target <;>
    cases hi : c.targetIsIndexField <;> cases hp : c.usesParallelIteration <;>
    cases hr : c.usesRepetitionNotUnique <;> cases hg : c.gateCanonical <;>
    rcases hv : c.valueCalculation with _ | v <;> (try cases v) <;>
    simp_all [DynEnumValueCalcRefusal.toRefusal] <;>
    subst_vars <;>
    simp_all [DynEnumRefusal.stage, DynEnumStage.order] <;>
    (try (cases violated <;> simp_all))

/-- A value-calculation class arriving is itself proof that every earlier stage passed — the
contrapositive a consumer reads when it sees one of the six and needs to know the model's world,
the target's declared type, and the gate are all already good. -/
theorem dynEnumLegality_valueCalc_implies_earlier_passed
    (c : DynEnumCandidate) (v : DynEnumValueCalcRefusal)
    (h : dynEnumLegality c = some v.toRefusal) :
    c.hModel = false ∧ targetTypeAdmits c.target = true ∧ c.targetIsIndexField = false ∧
      c.usesParallelIteration = false ∧ c.usesRepetitionNotUnique = false ∧
      c.gateCanonical = true := by
  unfold dynEnumLegality at h
  cases hm : c.hModel <;> cases ht : targetTypeAdmits c.target <;>
    cases hi : c.targetIsIndexField <;> cases hp : c.usesParallelIteration <;>
    cases hr : c.usesRepetitionNotUnique <;> cases hg : c.gateCanonical <;>
    simp_all <;> cases v <;> simp_all [DynEnumValueCalcRefusal.toRefusal]

/-- The reported class always belongs to the declared vocabulary, so a consumer switching over
`DynEnumRefusal.all` has no residual case. -/
theorem dynEnumLegality_mem_all (c : DynEnumCandidate) (r : DynEnumRefusal)
    (h : dynEnumLegality c = some r) : r ∈ DynEnumRefusal.all := by
  cases r <;> simp [DynEnumRefusal.all]

end A12Kernel
