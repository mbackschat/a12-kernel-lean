import A12Kernel.Elaboration.FirstFilledPlacement

/-! # Laws of the shared first-filled site

Every carrier placed on the site runs through `CheckedFirstFilledSite.instances`, so its address laws
are stated once here rather than once per carrier.
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

end A12Kernel
