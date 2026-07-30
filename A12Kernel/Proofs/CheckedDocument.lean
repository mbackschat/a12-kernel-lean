import A12Kernel.Elaboration.CheckedDocument

/-! # Checked-document row-environment laws -/

namespace A12Kernel

/-- One repeatable coordinate produces exactly its directly addressed row. -/
theorem repeatableAncestorRowsFor_singleton
    (level : RepeatableLevel) (coordinate : Nat) :
    repeatableAncestorRowsFor [level] [coordinate] = [{
      group := level
      path := [coordinate]
    }] := by
  rfl

/-- Nested repeatable coordinates accumulate the exact directly addressed path at each level. -/
theorem repeatableAncestorRowsFor_pair
    (outer inner : RepeatableLevel)
    (outerCoordinate innerCoordinate : Nat) :
    repeatableAncestorRowsFor [outer, inner]
        [outerCoordinate, innerCoordinate] = [
      { group := outer, path := [outerCoordinate] },
      { group := inner, path := [outerCoordinate, innerCoordinate] }
    ] := by
  rfl

private theorem env_bindingAt_cons_irrelevant
    (binding : RepeatableLevel × Nat) (environment : Env)
    (level : RepeatableLevel) (different : binding.1 ≠ level) :
    Env.bindingAt (binding :: environment) level =
      Env.bindingAt environment level := by
  unfold Env.bindingAt
  simp [different]

private theorem env_pathForScope_cons_irrelevant
    (binding : RepeatableLevel × Nat) (environment : Env)
    (scope : List RepeatableLevel) (outside : binding.1 ∉ scope) :
    Env.pathForScope (binding :: environment) scope =
      Env.pathForScope environment scope := by
  induction scope with
  | nil => rfl
  | cons level remaining inductionHypothesis =>
      have outsideParts :
          binding.1 ≠ level ∧ binding.1 ∉ remaining := by
        simpa using outside
      have different : binding.1 ≠ level := outsideParts.1
      have outsideRemaining : binding.1 ∉ remaining := outsideParts.2
      simp only [Env.pathForScope]
      rw [env_bindingAt_cons_irrelevant
        binding environment level different]
      cases environment.bindingAt level with
      | error error => rfl
      | ok coordinate =>
          rw [inductionHypothesis outsideRemaining]

/-- A complete unique scope resolves to exactly the environment's model-ordered coordinates. -/
theorem env_pathForScope_complete_nodup
    (environment : Env) (scope : List RepeatableLevel)
    (path : List Nat)
    (levels : environment.map Prod.fst = scope)
    (unique : scope.Nodup)
    (resolved : environment.pathForScope scope = .ok path) :
    path = environment.map Prod.snd := by
  induction scope generalizing environment path with
  | nil =>
      have empty : environment = [] := by
        simpa using congrArg List.length levels
      subst environment
      change Except.ok [] = Except.ok path at resolved
      cases resolved
      rfl
  | cons level remaining inductionHypothesis =>
      cases environment with
      | nil => simp at levels
      | cons binding tail =>
          have bindingLevel : binding.1 = level := by
            simpa using congrArg List.head? levels
          have tailLevels : tail.map Prod.fst = remaining := by
            simpa [bindingLevel] using congrArg List.tail levels
          have levelOutside : level ∉ remaining :=
            (List.nodup_cons.mp unique).1
          have bindingOutside : binding.1 ∉ remaining := by
            simpa [bindingLevel] using levelOutside
          have tailUnique : remaining.Nodup :=
            (List.nodup_cons.mp unique).2
          have tailFilter :
              tail.filter (fun candidate =>
                candidate.1 == binding.1) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro candidate member
            have candidateLevel : candidate.1 ∈ remaining := by
              rw [← tailLevels]
              exact List.mem_map.mpr
                ⟨candidate, member, rfl⟩
            intro same
            have sameLevel : candidate.1 = binding.1 := by
              simpa using same
            apply levelOutside
            simpa [bindingLevel, sameLevel] using candidateLevel
          simp only [Env.pathForScope] at resolved
          cases firstBinding :
              Env.bindingAt (binding :: tail) level with
          | error error =>
              simp [firstBinding, Bind.bind, Except.bind] at resolved
          | ok coordinate =>
              cases remainingPath :
                  Env.pathForScope (binding :: tail) remaining with
              | error error =>
                  simp [firstBinding, remainingPath, Bind.bind,
                    Except.bind] at resolved
              | ok tailPath =>
                  simp [firstBinding, remainingPath, Bind.bind,
                    Except.bind] at resolved
                  change
                    Except.ok (coordinate :: tailPath) =
                      Except.ok path at resolved
                  cases resolved
                  have coordinateOwned : coordinate = binding.2 := by
                    have tailFilterLevel :
                        tail.filter (fun candidate =>
                          candidate.1 == level) = [] := by
                      simpa [bindingLevel] using tailFilter
                    unfold Env.bindingAt at firstBinding
                    by_cases zero : binding.2 = 0
                    · simp [bindingLevel, tailFilterLevel,
                        zero] at firstBinding
                    · simp [bindingLevel, tailFilterLevel,
                        zero] at firstBinding
                      exact firstBinding.symm
                  have tailResolved :
                      Env.pathForScope tail remaining =
                        .ok tailPath := by
                    rw [← env_pathForScope_cons_irrelevant
                      binding tail remaining bindingOutside]
                    exact remainingPath
                  have tailOwned :=
                    inductionHypothesis tail tailPath tailLevels
                      tailUnique tailResolved
                  simp [coordinateOwned, tailOwned]

private theorem checkedRowEnvironmentProjection
    (scope : List RepeatableLevel) (rows : List RowAddr)
    (environments : List Env)
    (mapped :
      rows.mapM (fun row =>
        if row.path.length == scope.length then
          Except.ok (scope.zip row.path)
        else
          throw (.incoherentRow row : ActualRowEnvironmentError)) =
        Except.ok environments) :
    environments = rows.map (fun row => scope.zip row.path) ∧
      ∀ row ∈ rows, row.path.length = scope.length := by
  induction rows generalizing environments with
  | nil =>
      change Except.ok [] = Except.ok environments at mapped
      cases mapped
      simp
  | cons row remaining inductionHypothesis =>
      by_cases lengthMatches : row.path.length = scope.length
      · simp [lengthMatches, Bind.bind, Except.bind] at mapped
        cases remainingResult :
            remaining.mapM (fun candidate =>
              if candidate.path.length = scope.length then
                Except.ok (scope.zip candidate.path)
              else
                throw
                  (.incoherentRow candidate :
                    ActualRowEnvironmentError)) with
        | error error =>
            rw [remainingResult] at mapped
            contradiction
        | ok remainingEnvironments =>
            rw [remainingResult] at mapped
            change
              Except.ok
                  (scope.zip row.path :: remainingEnvironments) =
                Except.ok environments at mapped
            cases mapped
            have projected :=
              inductionHypothesis remainingEnvironments (by
                simpa using remainingResult)
            constructor
            · simp [projected.1]
            · intro candidate member
              rcases List.mem_cons.mp member with equal | member
              · simpa [equal] using lengthMatches
              · exact projected.2 candidate member
      · simp_all [Bind.bind, Except.bind]

private theorem checkedDocument_actualRowEnvironment_properties
    (checked : CheckedDocument model)
    (scope : List RepeatableLevel) (environments : List Env)
    (resolved :
      checked.actualRowEnvironments scope = .ok environments) :
    environments.Nodup ∧
      ∀ environment ∈ environments,
        environment.map Prod.fst = scope := by
  unfold CheckedDocument.actualRowEnvironments at resolved
  cases reversed : scope.reverse with
  | nil =>
      simp [reversed] at resolved
  | cons deepest remaining =>
      rw [reversed] at resolved
      dsimp only at resolved
      cases groupResult : model.repeatableGroupAtLevel? deepest with
      | none =>
          simp only [groupResult] at resolved
          simp_all [Bind.bind, Except.bind, Pure.pure, Except.pure]
      | some group =>
          simp only [groupResult] at resolved
          simp only [Bind.bind, Except.bind, Pure.pure,
            Except.pure] at resolved
          by_cases coherent :
              scope =
                model.repeatableScopeForGroupPath group.path
          · let rows :=
              checked.source.instantiatedRows.filter fun row =>
                row.group == deepest
            have mapped :
                rows.mapM (fun row =>
                  if row.path.length == scope.length then
                    Except.ok (scope.zip row.path)
                  else
                    throw
                      (.incoherentRow row :
                        ActualRowEnvironmentError)) =
                  Except.ok environments := by
              simpa [coherent, rows] using resolved
            have projected :=
              checkedRowEnvironmentProjection scope rows environments mapped
            constructor
            · rw [projected.1]
              have rowsNodup : rows.Nodup :=
                checked.rowsNodup.filter _
              rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
              refine List.Pairwise.imp_of_mem ?_ rowsNodup
              intro left right leftMember rightMember different equal
              apply different
              have leftGroup : left.group = deepest := by
                have filtered := (List.mem_filter.mp leftMember).2
                simpa using filtered
              have rightGroup : right.group = deepest := by
                have filtered := (List.mem_filter.mp rightMember).2
                simpa using filtered
              have leftLength := projected.2 left leftMember
              have rightLength := projected.2 right rightMember
              have pathsEqual :=
                congrArg (List.map Prod.snd) equal
              rw [List.map_snd_zip (Nat.le_of_eq leftLength),
                List.map_snd_zip (Nat.le_of_eq rightLength)] at pathsEqual
              cases left
              cases right
              simp_all
            · intro environment member
              rw [projected.1] at member
              rcases List.mem_map.mp member with
                ⟨row, rowMember, equal⟩
              subst environment
              apply List.map_fst_zip
              exact Nat.le_of_eq
                (projected.2 row rowMember).symm
          · simp_all

/-- Successful actual-row projection preserves the checked document's physical row uniqueness. -/
theorem checkedDocument_actualRowEnvironments_nodup
    (checked : CheckedDocument model)
    (scope : List RepeatableLevel) (environments : List Env)
    (resolved :
      checked.actualRowEnvironments scope = .ok environments) :
    environments.Nodup :=
  (checkedDocument_actualRowEnvironment_properties
    checked scope environments resolved).1

/-- Every actual-row environment contains exactly the requested scope levels in model order. -/
theorem checkedDocument_actualRowEnvironment_scope
    (checked : CheckedDocument model)
    (scope : List RepeatableLevel) (environments : List Env)
    (resolved :
      checked.actualRowEnvironments scope = .ok environments)
    (environment : Env) (member : environment ∈ environments) :
    environment.map Prod.fst = scope :=
  (checkedDocument_actualRowEnvironment_properties
    checked scope environments resolved).2 environment member

end A12Kernel
