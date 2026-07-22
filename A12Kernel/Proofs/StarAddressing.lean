import A12Kernel.Semantics.StarAddressing

namespace A12Kernel

/-- A star on the first repeatable axis never inherits a current-row binding. -/
@[simp] theorem starPath_firstAxis_reopens (axis : StarAxis) (axes : List StarAxis) (outer : Env) :
    (StarPath.mk (axis :: axes) 0).boundEnvironment outer = .ok [] := by
  rfl

/-- The common stream bridge reads exactly once per resolved leaf and preserves its canonical order. -/
@[simp] theorem resolvedStarTopology_cells (resolved : ResolvedStarTopology)
    (read : Env → ValueListCell kind) (hasHaving : Bool) :
    (resolved.toResolvedSide read hasHaving).cells = resolved.environments.map read := by
  rfl

/-- Stream classification cannot change the hierarchical omitted-tail decision built from the same topology. -/
@[simp] theorem resolvedStarTopology_tail (resolved : ResolvedStarTopology)
    (read : Env → ValueListCell kind) (hasHaving : Bool) :
    (resolved.toResolvedSide read hasHaving).hasUninstantiatedTail = resolved.domain.hasOpenTail := by
  rfl

end A12Kernel
