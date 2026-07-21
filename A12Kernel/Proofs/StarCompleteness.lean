import A12Kernel.Semantics.StarCompleteness

/-! # Reopened-star completeness laws

These laws characterize structural tail completeness after the first-star binding
decision. They do not prove authored path resolution, repetition-tree construction,
selected-cell classification, or external kernel correspondence.
-/

namespace A12Kernel

/-- A selected deepest row is structurally complete; its cell can still be empty in the
    separate resolved stream. -/
@[simp] theorem reopenedStar_selectedLeaf_closed :
    ReopenedStarDomain.selectedLeaf.hasOpenTail = false := by
  rfl

/-- No finite document can exhaust an unbounded reopened repetition. -/
@[simp] theorem reopenedStar_unbounded_open (rows : ReopenedStarRows) :
    (ReopenedStarDomain.repeatable none rows).hasOpenTail = true := by
  rfl

/-- A finite reopened level is closed exactly when its actual row count reaches the cap
    and every actual child subtree is closed. -/
theorem reopenedStar_finite_closed_iff
    (repeatability : Nat) (rows : ReopenedStarRows) :
    (ReopenedStarDomain.repeatable (some repeatability) rows).hasOpenTail = false ↔
      (rows.length < repeatability) = false ∧ rows.hasOpenTail = false := by
  simp [ReopenedStarDomain.hasOpenTail]

/-- One open child makes its parent-row list open independently of every later sibling. -/
theorem reopenedStarRows_open_of_head
    (coordinate : Nat) (child : ReopenedStarDomain) (rest : ReopenedStarRows)
    (openChild : child.hasOpenTail = true) :
    (ReopenedStarRows.cons coordinate child rest).hasOpenTail = true := by
  simp [ReopenedStarRows.hasOpenTail, openChild]

/-- Structural tail completeness is independent of the concrete coordinate labels once
    checked lowering has supplied one entry per actual child row. -/
theorem reopenedStarRows_coordinate_irrelevant
    (left right : Nat) (child : ReopenedStarDomain) (rest : ReopenedStarRows) :
    (ReopenedStarRows.cons left child rest).hasOpenTail =
      (ReopenedStarRows.cons right child rest).hasOpenTail := by
  rfl

/-- The hierarchical result enters the existing resolved boundary as exactly its
    uninstantiated-tail component. -/
theorem reopenedStar_toResolvedSide_tail
    (domain : ReopenedStarDomain) (cells : List (ValueListCell kind))
    (hasHaving : Bool) :
    (domain.toResolvedSide cells hasHaving).hasUninstantiatedTail =
      domain.hasOpenTail := by
  rfl

/-- Empty selected cells and hierarchical structural tails remain independent inputs and
    compose through the existing missing-potential disjunction. -/
theorem reopenedStar_toResolvedSide_missingPotential
    (domain : ReopenedStarDomain) (cells : List (ValueListCell kind))
    (hasHaving : Bool) :
    (domain.toResolvedSide cells hasHaving).hasMissingPotential =
      (cells.any ValueListCell.isEmpty || domain.hasOpenTail) := by
  rfl

end A12Kernel
