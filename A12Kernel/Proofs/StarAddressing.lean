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

/-- Two environments agreeing at every level of a scope project that scope identically, failures
    included. This is the step that turns level-wise agreement into address equality. -/
theorem env_pathForScope_congr (left right : Env) (scope : List RepeatableLevel)
    (agree : ∀ level ∈ scope, left.bindingAt level = right.bindingAt level) :
    left.pathForScope scope = right.pathForScope scope := by
  induction scope with
  | nil => rfl
  | cons level levels induction =>
      have tail : left.pathForScope levels = right.pathForScope levels :=
        induction fun named member => agree named (List.mem_cons_of_mem _ member)
      simp only [Env.pathForScope, agree level List.mem_cons_self, tail]

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

/-- One bound axis uses the shared named environment lookup; unrelated binding order cannot affect the retained prefix. -/
theorem starPath_boundEnvironment_single (axis : StarAxis)
    (axes : List StarAxis) (outer : Env) (coordinate : Nat)
    (binding : outer.bindingAt axis.level = .ok coordinate) :
    (StarPath.mk (axis :: axes) 1).boundEnvironment outer =
      .ok [(axis.level, coordinate)] := by
  unfold StarPath.boundEnvironment
  simp only [List.take, List.mapM_cons, List.mapM_nil]
  rw [binding]
  rfl

/-- A duplicate required outer binding fails structurally instead of selecting one occurrence. -/
theorem starPath_boundEnvironment_duplicate (axis : StarAxis)
    (axes : List StarAxis) (outer : Env)
    (binding :
      outer.bindingAt axis.level =
        .error (.duplicateBinding axis.level)) :
    (StarPath.mk (axis :: axes) 1).boundEnvironment outer =
      .error (.duplicateBinding axis.level) := by
  unfold StarPath.boundEnvironment
  simp only [List.take, List.mapM_cons, List.mapM_nil]
  rw [binding]
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

/-! ### A candidate environment differs from its captured prefix only where the path reopens

This is why a filter's `$` marker is **semantically redundant** on a level the starred operand does
not reopen: the candidate environment inherits that level's coordinate from the bound prefix
unchanged, so the marked and unmarked spellings resolve the same address. The kernel admits both
spellings there and they fire on identical rows
([checkpoint](../../docs/sources/having-filter-probes.md#src-bare-outer-reference-redundant-marker)).
Stating it here rather than at the filter keeps it a property of the addressing, which is where the
inheritance actually happens. -/

/-- Extending an environment cannot change a level the extension does not bind. `bindingAt` filters
    by level, so the extension contributes nothing to the filtered list. -/
theorem env_bindingAt_append_unbound (base extension : Env) (level : RepeatableLevel)
    (unbound : ∀ binding ∈ extension, binding.1 ≠ level) :
    (base ++ extension).bindingAt level = base.bindingAt level := by
  have empty : extension.filter (fun binding => binding.1 == level) = [] := by
    rw [List.filter_eq_nil_iff]
    intro binding member
    simpa using unbound binding member
  simp only [Env.bindingAt, List.filter_append, empty, List.append_nil]

mutual
  /-- Every leaf environment of a reopened tree agrees with its bound prefix at any level the tree's
      own axes do not name. -/
  theorem starDomain_environments_agreeOutside
      {levels : List RepeatableLevel} {base : Env} {domain : ReopenedStarDomain}
      {environments : List Env}
      (correspondence :
        ReopenedStarDomain.EnvironmentCorrespondence levels base domain environments)
      (level : RepeatableLevel) (outside : level ∉ levels) :
      ∀ candidate ∈ environments, candidate.bindingAt level = base.bindingAt level := by
    cases correspondence with
    | selected base =>
        intro candidate member
        cases List.mem_singleton.1 member
        rfl
    | repeatable axisLevel levels base repeatability rows environments rowCorrespondence =>
        exact starRows_environments_agreeOutside rowCorrespondence level
          (fun named => outside (List.mem_cons_of_mem _ named))
          (fun named => outside (named ▸ List.mem_cons_self))

  /-- The sibling companion. Each row's child extends the same prefix by its own axis level only. -/
  theorem starRows_environments_agreeOutside
      {axisLevel : RepeatableLevel} {levels : List RepeatableLevel} {base : Env}
      {rows : ReopenedStarRows} {environments : List Env}
      (correspondence :
        ReopenedStarRows.EnvironmentCorrespondence axisLevel levels base rows environments)
      (level : RepeatableLevel) (outsideDeeper : level ∉ levels)
      (outsideAxis : level ≠ axisLevel) :
      ∀ candidate ∈ environments, candidate.bindingAt level = base.bindingAt level := by
    cases correspondence with
    | nil => intro candidate member; cases member
    | cons axisLevel levels base coordinate child rest childEnvironments restEnvironments
        childCorrespondence restCorrespondence =>
        intro candidate member
        rcases List.mem_append.1 member with fromChild | fromRest
        · have inherited := starDomain_environments_agreeOutside childCorrespondence level
            outsideDeeper candidate fromChild
          rw [inherited]
          exact env_bindingAt_append_unbound base [(axisLevel, coordinate)] level
            (by
              intro binding member
              cases List.mem_singleton.1 member
              exact fun named => outsideAxis named.symm)
        · exact starRows_environments_agreeOutside restCorrespondence level outsideDeeper
            outsideAxis candidate fromRest
end

/-- The consumer-facing form: for a level the resolved path does **not** reopen, every candidate
    environment carries the bound prefix's own coordinate. A filter reference whose declared scope
    avoids the reopened levels therefore resolves identically marked or unmarked. -/
theorem starPath_resolve_agreeOutsideReopened
    (path : StarPath) (document : Document) (outer bound : Env)
    (resolved : ResolvedStarTopology)
    (resolution : path.resolve document outer = .ok resolved)
    (boundEnvironment : path.boundEnvironment outer = .ok bound)
    (level : RepeatableLevel)
    (outside : level ∉ (path.axes.drop path.firstStar).map (·.level)) :
    ∀ candidate ∈ resolved.environments,
      candidate.bindingAt level = bound.bindingAt level := by
  obtain ⟨actual, actualBound, correspondence⟩ :=
    StarPath.resolve_environmentCorrespondence path document outer resolved resolution
  rw [boundEnvironment] at actualBound
  cases actualBound
  exact starDomain_environments_agreeOutside correspondence level outside

end A12Kernel
