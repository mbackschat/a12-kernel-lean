import A12Kernel.Elaboration.FieldFillList

/-! # `NumberOfFilledFields` extent and partial-read laws

The extent laws separate declared capacity from instantiated cells. Partial-read prefix laws retain
the first unavailable result without consulting later addresses.
-/

namespace A12Kernel

theorem countPartialFieldReads_silent_prefix
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (environment : Env) (field : FieldId) (rest : List (Env × FieldId))
    (unavailable : read environment field = .ok none) :
    countPartialFieldReads read ((environment, field) :: rest) = .ok .silentlyUnavailable := by
  simp [countPartialFieldReads, unavailable, bind, Except.bind, pure, Except.pure]

theorem countPartialFieldReads_unknown_prefix
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (environment : Env) (field : FieldId) (rest : List (Env × FieldId))
    (cell : CheckedCell) (cause : FormalCause)
    (available : read environment field = .ok (some cell))
    (unknown : observeCell .validation cell = .unknown cause) :
    countPartialFieldReads read ((environment, field) :: rest) = .ok (.evaluated .unknown) := by
  simp [countPartialFieldReads, available, unknown, numberOfFilledFields,
    bind, Except.bind, pure, Except.pure]

private theorem slotCapacityFold_flat (model : FlatModel) (enclosing : Nat) :
    ∀ (declarations : List FlatFieldDecl) (accumulated : Nat),
      (∀ declaration ∈ declarations,
        declaration.repeatableScope.drop enclosing = []) →
      declarations.foldl
        (fun total declaration =>
          total.bind fun carried =>
            (model.declarationSlots? enclosing declaration).map (carried + ·))
        (some accumulated)
        = some (accumulated + declarations.length) := by
  intro declarations
  induction declarations with
  | nil => intro accumulated _; simp
  | cons head tail ih =>
      intro accumulated flat
      have headSlot : model.declarationSlots? enclosing head = some 1 := by
        simp [FlatModel.declarationSlots?, flat head (by simp)]
      simp only [List.foldl_cons, headSlot, Option.bind_some, Option.map_some]
      rw [ih (accumulated + 1) (fun declaration member => flat declaration (by simp [member]))]
      show some (accumulated + 1 + tail.length) = _
      simp only [List.length_cons]
      congr 1
      omega

/-- Declared slot capacity collapses to the declaration count exactly on a subtree with no repeatable
descendant of its own. This is the coincidence that let a movement rule keyed on the declaration
count look correct: every fixture without a repeatable descendant satisfies this hypothesis, and on
those the two readings are literally the same number. Stated as a law so a consumer can see the
condition under which the cheap count is safe, rather than rediscovering it from a wrong row. -/
theorem flatModel_groupSubtreeSlotCapacity_eq_fieldCount_ofNoRepeatableDescendant
    (model : FlatModel) (path : GroupPath)
    (flat : ∀ declaration ∈ model.groupSubtreeFields path,
      declaration.repeatableScope.drop
        (model.repeatableScopeForGroupPath path).length = []) :
    model.groupSubtreeSlotCapacity? path =
      some (model.groupSubtreeFields path).length := by
  simp only [FlatModel.groupSubtreeSlotCapacity?, FlatModel.declarationsSlotCapacity?]
  simpa using slotCapacityFold_flat model
    (model.repeatableScopeForGroupPath path).length
    (model.groupSubtreeFields path) 0 flat

/-- One repeatable descendant row already separates the two readings, so the collapse above is a
genuine special case rather than the general rule. A single field under a `max n` descendant admits
`n` slots and one declaration. -/
theorem flatModel_declarationSlots_repeatableDescendant
    (model : FlatModel) (enclosing : Nat) (declaration : FlatFieldDecl)
    (level : RepeatableLevel) (capacity : Nat)
    (only : declaration.repeatableScope.drop enclosing = [level])
    (retained : (model.repeatableGroupAtLevel? level).bind (·.repeatability) =
      some capacity) :
    model.declarationSlots? enclosing declaration = some capacity := by
  simp only [FlatModel.declarationSlots?, only, List.foldl_cons, List.foldl_nil,
    Option.bind_some]
  cases hGroup : model.repeatableGroupAtLevel? level with
  | none => simp [hGroup] at retained
  | some group =>
      simp only [hGroup, Option.bind_some] at retained
      cases hCapacity : group.repeatability with
      | none => simp [hCapacity] at retained
      | some declared =>
          simp only [hCapacity] at retained
          simp [hCapacity, Option.some.inj retained]


/-- The instantiated tally contributes no declared-tail slots, so adding model capacity later
cannot double-count them. Formal unknowns remain instantiated classifications. -/
theorem checkedFieldFillList_tally_uninstantiated_zero
    (list : CheckedFieldFillList model)
    (document : CheckedDocument model) (outer : Env)
    (tally : ValidationFillTally)
    (resolved : list.validationFillTally document outer = .ok tally) :
    tally.uninstantiated = 0 := by
  unfold CheckedFieldFillList.validationFillTally at resolved
  cases core : list.observations document outer with
  | error error => simp [core, bind, Except.bind] at resolved
  | ok observations =>
      rw [core] at resolved
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at resolved
      subst resolved
      suffices general :
          ∀ (start : ValidationFillTally) (remaining : List CellObservation),
            start.uninstantiated = 0 →
              (remaining.foldl (init := start) fun tally observation =>
                tally.combine observation.asValidationFillTally).uninstantiated = 0 by
        exact general _ observations rfl
      intro start remaining
      induction remaining generalizing start with
      | nil => intro zero; exact zero
      | cons head rest hypothesis =>
          intro zero
          refine hypothesis _ ?_
          cases head <;> simp [ValidationFillTally.combine, CellObservation.asValidationFillTally, zero]

/-- With retained capacity, every operator over an unfiltered, unindexed list is the shared validation evaluator on the
same instantiated classifications plus the missing declared slots. This also preserves the four
operators whose result ignores the tail. -/
theorem checkedFieldFillList_fill_with_declared_capacity
    (list : CheckedFieldFillList model)
    (document : CheckedDocument model) (outer : Env)
    (operator : FieldFillQuantifier) (tally : ValidationFillTally) (capacity : Nat)
    (unfiltered : list.hasHaving = false) (unindexed : list.hasIndexed = false)
    (resolved : list.validationFillTally document outer = .ok tally)
    (available : list.fillCapacity? = some capacity) :
    list.evaluateFill? operator document outer =
      .ok (some (operator.evalValidation { tally with
        uninstantiated := capacity - (tally.filled + tally.empty + tally.unknown) })) := by
  cases operator <;>
    simp [CheckedFieldFillList.evaluateFill?, unfiltered, unindexed, resolved, available, FieldFillQuantifier.evalValidation,
      bind, Except.bind, pure, Except.pure]

/-- A group operand's list reads the group source's own declared slots, so the capacity theorem
above specializes to a group with the group's capacity. -/
theorem asFieldFillList_fillCapacity (checked : CheckedFilledFieldCountGroupSource model) :
    checked.asFieldFillList.fillCapacity? = checked.fillCapacity? := by
  cases h : checked.fillCapacity? <;>
    simp [CheckedFilledFieldCountGroupSource.asFieldFillList, CheckedFieldFillList.fillCapacity?,
      CheckedFieldFillList.sum?, CheckedFieldFillOperand.fillCapacity?, h]

end A12Kernel
