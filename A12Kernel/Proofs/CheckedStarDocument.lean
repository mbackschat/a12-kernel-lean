import A12Kernel.Elaboration.CheckedStarDocument

namespace A12Kernel

/-- A topology failure is preserved exactly and prevents every checked-document read. -/
theorem resolveCheckedField_addressing_error
    (source : CheckedStarFieldPath model) (checked : CheckedDocument model)
    (outer : Env) (cause : StarAddressingError)
    (failed :
      source.path.resolve checked.source.toDocument outer = .error cause) :
    source.resolveCheckedField checked outer = .error (.addressing cause) := by
  unfold CheckedStarFieldPath.resolveCheckedField
  rw [failed]
  simp only [Except.mapError, bind, Except.bind]

/-- A topology with no concrete leaf produces no addressed cell; an omitted declared tail remains only in the retained hierarchical domain. -/
theorem resolveCheckedField_empty_topology
    (source : CheckedStarFieldPath model) (checked : CheckedDocument model)
    (outer : Env) (topology : ResolvedStarTopology)
    (resolved :
      source.path.resolve checked.source.toDocument outer = .ok topology)
    (empty : topology.environments = []) :
    match source.resolveCheckedField checked outer with
    | .ok projected =>
        projected.topology = topology ∧ projected.cells = []
    | .error _ => False := by
  unfold CheckedStarFieldPath.resolveCheckedField
  rw [resolved]
  simp only [Except.mapError, bind, Except.bind]
  rw [empty]
  simp [pure, Except.pure]

end A12Kernel
