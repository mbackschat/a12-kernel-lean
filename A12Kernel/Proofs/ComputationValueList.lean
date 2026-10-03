import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel

namespace ValueListCell

/-- A deciding present cell excludes every later formal cause from this scan. -/
theorem anyComputation_deciding_prefix
    (predicate : ValueListAtom kind → Bool) (value : ValueListAtom kind)
    (suffix : List (ValueListCell kind)) (decides : predicate value = true) :
    anyComputation predicate (.present value :: suffix) = .ok true := by
  simp [anyComputation, decides]

/-- A reached invalid cell excludes every later match from this scan. -/
theorem anyComputation_poison_prefix
    (predicate : ValueListAtom kind → Bool) (cause : FormalCause)
    (suffix : List (ValueListCell kind)) :
    anyComputation predicate (.unknown cause :: suffix) = .error cause := rfl

/-- Empty cells do not change any present-value fold or its accumulator. -/
theorem scanPresent_emptyCells (step : state → ValueListAtom kind → state)
    (cells : List (ValueListCell kind)) (acc : state)
    (emptyCells : ∀ cell ∈ cells, cell = .empty) :
    scanPresent step cells acc = .ok acc := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      have first := emptyCells cell (by simp)
      subst cell
      exact ih (fun c member => emptyCells c (by simp [member]))

/-- An empty-cell existential scan observes no present value and no poison. -/
theorem anyComputation_emptyCells (predicate : ValueListAtom kind → Bool)
    (cells : List (ValueListCell kind)) (emptyCells : ∀ cell ∈ cells, cell = .empty) :
    anyComputation predicate cells = .ok false := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      have first := emptyCells cell (by simp)
      subst cell
      exact ih (fun c member => emptyCells c (by simp [member]))

end ValueListCell

namespace ValueListQuantifier

/-- Member operands containing only empty cells leave the collector unchanged. -/
theorem collectOperands_emptyCells
    (resolve : value → Except error (ResolvedValueListSide kind))
    (values : List value) (acc : List (ValueListAtom kind))
    (emptyMembers : ∀ v ∈ values, ∃ side, resolve v = .ok side ∧ ∀ c ∈ side.cells, c = .empty) :
    collectOperands resolve values acc = .ok (.ok acc) := by
  induction values generalizing acc with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨side, resolved, emptyCells⟩ := emptyMembers first (by simp)
      simp only [collectOperands, resolved, bind, Except.bind,
        ValueListCell.scanPresent_emptyCells _ _ _ emptyCells]
      exact ih acc (fun v member => emptyMembers v (by simp [member]))

/-- A resolved empty-cell side never decides an existential scan. -/
theorem anyOperands_emptyCells
    (resolve : value → Except error (ResolvedValueListSide kind))
    (predicate : ValueListAtom kind → Bool) (values : List value)
    (emptyValues : ∀ v ∈ values, ∃ side, resolve v = .ok side ∧ ∀ c ∈ side.cells, c = .empty) :
    anyOperands resolve predicate values = .ok (.ok false) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨side, resolved, emptyCells⟩ := emptyValues first (by simp)
      simp only [anyOperands, resolved, bind, Except.bind,
        ValueListCell.anyComputation_emptyCells _ _ emptyCells]
      exact ih (fun v member => emptyValues v (by simp [member]))

/-- Empty member cells decide AtLeastOne without resolving any subject, even a failing one. -/
theorem atLeastOne_emptyMemberCells
    (resolveField : field → Except error (ResolvedValueListSide kind))
    (resolveValue : value → Except error (ResolvedValueListSide kind))
    (fields : List field) (values : List value)
    (emptyMembers : ∀ v ∈ values, ∃ side, resolveValue v = .ok side ∧ ∀ c ∈ side.cells, c = .empty) :
    ValueListQuantifier.atLeastOne.evalComputationWith resolveField resolveValue fields values = .ok .notTrue := by
  simp [evalComputationWith, collectOperands_emptyCells resolveValue values [] emptyMembers,
    bind, Except.bind, pure, Except.pure]

/-- NotAll's presence prepass skips the member side when all subject cells are empty. -/
theorem notAll_emptySubjectCells
    (resolveField : field → Except error (ResolvedValueListSide kind))
    (resolveValue : value → Except error (ResolvedValueListSide kind))
    (fields : List field) (values : List value)
    (emptyFields : ∀ f ∈ fields, ∃ side, resolveField f = .ok side ∧ ∀ c ∈ side.cells, c = .empty) :
    ValueListQuantifier.notAll.evalComputationWith resolveField resolveValue fields values = .ok .notTrue := by
  simp [evalComputationWith, anyOperands_emptyCells resolveField (fun _ => true) fields emptyFields,
    bind, Except.bind, pure, Except.pure]

/-- An empty member side decides AtLeastOne before any field is read. -/
theorem atLeastOne_empty_members
    (fields : List (ResolvedValueListSide kind)) :
    ValueListQuantifier.atLeastOne.evalComputation fields [] = .notTrue := rfl

end ValueListQuantifier

end A12Kernel
