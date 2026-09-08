import A12Kernel.Elaboration.OperandAddressingScope

/-! # Laws of the operand addressing and scope gates

`wildcardPlacement_lenience_splits_the_two` is the consumer-facing law: lenience moves exactly one of the
two star gates, so a lenient reader cannot assume the strict vocabulary minus a uniform relaxation.

`unresolvedName_partitions_by_depth` says the two unresolvable-name classes are a partition of one
condition rather than two diagnoses, which is what a repair tool needs in order not to look for two
different faults.

The membership laws pin both edges of the parent-path test, the one that admits arbitrarily deep
descendants and the one that excludes the scoping group itself.
-/

namespace A12Kernel

/-- **Lenience moves exactly one of the two star gates.** -/
theorem wildcardPlacement_lenience_splits_the_two :
    wildcardPlacementRefusal false .relativeStep = some .wildcardOnRelativeStep ∧
      wildcardPlacementRefusal true .relativeStep = none ∧
      (∀ lenient, wildcardPlacementRefusal lenient .ruleContext = some .wildcardOnRuleContext) := by
  refine ⟨rfl, rfl, ?_⟩
  intro lenient; rfl

/-- **The unresolvable-name classes partition by depth**, so exactly one is reported and which one is
decided by the candidate alone. -/
theorem unresolvedName_partitions_by_depth (candidate : EntityPath) :
    (unresolvedNameRefusal candidate = .invalidRootGroup ↔ candidate.length ≤ 1) ∧
      (unresolvedNameRefusal candidate = .invalidEntity ↔ ¬ candidate.length ≤ 1) := by
  constructor <;> · unfold unresolvedNameRefusal; split <;> simp_all

/-- A descendant at **any** depth lies within the scope, so the guard is not a direct-child test. -/
theorem withinGroup_admits_any_descendant (scope below : EntityPath) (leaf : String) :
    withinGroup scope (scope ++ below ++ [leaf]) = true := by
  simp [withinGroup, List.isPrefixOf_iff_prefix]

/-- The scoping group itself is **not** within its own scope, because its parent lies above it. -/
theorem withinGroup_excludes_the_scope_itself (parent : EntityPath) (name : String) :
    withinGroup (parent ++ [name]) (parent ++ [name]) = false := by
  simp only [withinGroup, List.dropLast_concat]
  cases h : List.isPrefixOf (parent ++ [name]) parent with
  | false => rfl
  | true =>
      -- a prefix is no longer than its host, and this one is one segment longer
      have hlen := (List.isPrefixOf_iff_prefix.mp h).length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega

/-- A list refuses exactly when some member lies outside, so the guard is a conjunction over members and
an empty list is admitted. -/
theorem groupScopeRefusal_iff (scope : EntityPath) (members : List EntityPath) :
    groupScopeRefusal scope members = none ↔ ∀ member ∈ members, withinGroup scope member = true := by
  simp [groupScopeRefusal, List.all_eq_true]

/-- The shared-root-group guard is silent for every A12 call site, which is the modelled content of its
unreachability claim. -/
theorem sharedRootGroup_silent_outside_hModel (roots : List String) :
    sharedRootGroupRefusal false roots = none := by
  simp [sharedRootGroupRefusal]

end A12Kernel
