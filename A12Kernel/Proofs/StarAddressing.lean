import A12Kernel.Semantics.StarAddressing

namespace A12Kernel

/-- A successful named environment projection has exactly one coordinate per requested model scope level. -/
theorem env_pathForScope_length (environment : Env)
    (scope : List RepeatableLevel) (path : List Nat)
    (resolved : environment.pathForScope scope = .ok path) :
    path.length = scope.length := by
  induction scope generalizing path with
  | nil =>
      simp [Env.pathForScope, pure, Except.pure] at resolved
      simp [← resolved]
  | cons level levels induction =>
      simp only [Env.pathForScope] at resolved
      cases binding : environment.bindingAt level with
      | error cause =>
          simp [binding, bind, Except.bind] at resolved
      | ok coordinate =>
          cases remaining : environment.pathForScope levels with
          | error cause =>
              simp [binding, remaining, bind, Except.bind] at resolved
          | ok tail =>
              simp [binding, remaining, bind, Except.bind, pure, Except.pure]
                at resolved
              subst path
              simp [induction tail remaining]

/-- One positive singleton binding projects to its exact coordinate; no positional default is involved. -/
theorem env_pathForScope_singleton (level : RepeatableLevel) (coordinate : Nat)
    (positive : coordinate ≠ 0) :
    Env.pathForScope [(level, coordinate)] [level] = .ok [coordinate] := by
  simp [Env.pathForScope, Env.bindingAt, positive, bind, Except.bind,
    pure, Except.pure]

/-- The shared structural overlay replaces any prior scalar result with the exact over-repetition finding. -/
@[simp] theorem withOverRepetitionIf_true {α : Type}
    (cell : CheckedCell α) :
    cell.withOverRepetitionIf true =
      { cell with parsed := none, findings := [.overRepetition] } := by
  rfl

/-- An in-cap address leaves every scalar result unchanged. -/
@[simp] theorem withOverRepetitionIf_false {α : Type}
    (cell : CheckedCell α) :
    cell.withOverRepetitionIf false = cell := by
  rfl

/-- The structural overlay preserves the checked-cell placement/value invariant for either capacity branch. -/
theorem withOverRepetitionIf_preserves_wellFormed {α : Type}
    (cell : CheckedCell α) (overLimit : Bool)
    (wellFormed : cell.WellFormed) :
    (cell.withOverRepetitionIf overLimit).WellFormed := by
  cases overLimit with
  | false =>
      simpa [CheckedCell.withOverRepetitionIf] using wellFormed
  | true =>
      simp [CheckedCell.withOverRepetitionIf, CheckedCell.WellFormed]

/-- Over-repetition has the shared validation face independently of the scalar result it replaced. -/
@[simp] theorem observe_withOverRepetition_validation {α : Type}
    (cell : CheckedCell α) :
    observeCell .validation (cell.withOverRepetitionIf true) =
      .unknown .overRepetition := by
  rfl

/-- Over-repetition has the shared computation-poison face independently of the scalar result it replaced. -/
@[simp] theorem observe_withOverRepetition_computation {α : Type}
    (cell : CheckedCell α) :
    observeCell .computation (cell.withOverRepetitionIf true) =
      .poison .overRepetition := by
  rfl

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
