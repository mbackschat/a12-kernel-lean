import A12Kernel.Elaboration.FirstFilledPlacement

/-! # Laws of the shared first-filled site

Every carrier placed on the site runs through `CheckedFirstFilledSite.instances` and reads the
site's source, so its placement laws are stated once here rather than once per carrier: a fixed
target's single instance, and a repeatable target's one bound sibling star.
-/

namespace A12Kernel

/-- A fixed target runs exactly once, at its single instance, the empty environment. -/
theorem firstFilledSite_instances_fixed {Outcome Fault : Type}
    (site : CheckedFirstFilledSite model) (input : CheckedDocument model)
    (onRowError : ActualRowEnvironmentError → Fault) (onEnvironment : EnvBindingError → Fault)
    (clearOnly produce : CellAddr → Env → Except Fault Outcome)
    (fixed : site.target.repeatableScope = []) :
    site.instances input onRowError onEnvironment clearOnly produce =
      (·::[]) <$> produce { field := site.targetField, path := [] } [] := by
  simp [CheckedFirstFilledSite.instances, CheckedDocument.computationTargetOutcomes, fixed,
    Env.pathForScope]
  rfl

/-- A repeatable target reads one sibling star: one reopened axis, below a nonempty binding whose
every level the target's own row binds. -/
theorem firstFilledSite_repeatable_readsBoundSiblingStar (site : CheckedFirstFilledSite model)
    (repeatable : site.target.repeatableScope ≠ []) :
    ∃ star, site.source = .star star ∧ star.reopenedScope.length = 1 ∧ star.bindingScope ≠ [] ∧
      star.bindingScope.all site.target.repeatableScope.contains = true := by
  obtain ⟨targetField, target, owned, source, declaringGroup, valid, placement⟩ := site
  cases placement with
  | fixed fixed _ => exact absurd fixed repeatable
  | rows _ _ placement =>
      exact ⟨_, rfl, placement.sourceSingleReopenedAxis, placement.sourceBindingNonempty,
        placement.sourceBindingBound⟩

end A12Kernel
