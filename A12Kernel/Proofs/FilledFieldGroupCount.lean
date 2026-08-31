import A12Kernel.Elaboration.FilledFieldGroupCount

/-! # Group-scope `NumberOfFilledFields` extent laws

These laws are about the *extent* a group operand's count moves against, not about the count itself.
They exist because the extent has two plausible readings that agree on most models, and the wrong one
shipped here until a kernel row separated them.
-/

namespace A12Kernel

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
  simp only [FlatModel.groupSubtreeSlotCapacity?]
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


/-- A group operand's validation tally reports **no** uninstantiated slot, because its resolved core
enumerates instantiated rows only. This is the quantity that puts `AllFieldsFilled`,
`NotAllFieldsFilled`, and `FieldsNotCollectivelyFilled` outside `GroupFieldFillQuantifier`: each
reads that field, and each would therefore answer from a zero that means *not enumerated* rather
than *no declared tail*. -/
theorem checkedFilledFieldCountGroupSource_tally_uninstantiated_zero
    (checked : CheckedFilledFieldCountGroupSource model)
    (document : CheckedDocument model) (outer : Env)
    (tally : ValidationFillTally)
    (resolved : checked.validationFillTally document outer = .ok tally) :
    tally.uninstantiated = 0 := by
  unfold CheckedFilledFieldCountGroupSource.validationFillTally at resolved
  cases core :
      document.resolveCheckedGroupEntityOperandCore outer
        checked.source.boundLevelCount checked.declarations with
  | error error => simp [core, bind, Except.bind] at resolved
  | ok value =>
      rw [core] at resolved
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at resolved
      subst resolved
      generalize value.inCapacityAddressedCells = cells
      suffices general :
          ∀ (start : ValidationFillTally) (remaining : List CheckedAddressedCell),
            start.uninstantiated = 0 →
              (remaining.foldl (init := start) fun tally addressed =>
                tally.combine
                  (observeCell .validation addressed.cell).asValidationFillTally).uninstantiated =
                0 by
        exact general _ cells rfl
      intro start remaining
      induction remaining generalizing start with
      | nil => intro zero; exact zero
      | cons head rest hypothesis =>
          intro zero
          refine hypothesis _ ?_
          cases observation : observeCell .validation head.cell <;>
            simp [ValidationFillTally.combine, observation, zero]

end A12Kernel
