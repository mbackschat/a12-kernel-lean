import A12Kernel.Semantics.ValueList

/-! # Reopened-star structural completeness

This capsule starts at the first starred repeatable level after path checking and scope
binding. It retains actual rows under their actual parent without materializing the
declared Cartesian product. Cell classification remains in `ResolvedValueListSide`;
this tree derives only the declared-but-uninstantiated tail bit.
-/

namespace A12Kernel

mutual
  /-- The repeatable levels reopened by one starred operand. A selected leaf represents
      one actual deepest row; its field cell remains in the separate resolved stream. -/
  inductive ReopenedStarDomain where
    | selectedLeaf
    | repeatable (repeatability : Option Nat) (rows : ReopenedStarRows)

  /-- Actual child rows under one actual parent, retaining their 1-based coordinates. -/
  inductive ReopenedStarRows where
    | nil
    | cons (coordinate : Nat) (child : ReopenedStarDomain) (rest : ReopenedStarRows)
end

namespace ReopenedStarRows

def length : ReopenedStarRows → Nat
  | .nil => 0
  | .cons _ _ rest => rest.length + 1

def containsCoordinate (coordinate : Nat) : ReopenedStarRows → Bool
  | .nil => false
  | .cons found _ rest => coordinate == found || rest.containsCoordinate coordinate

end ReopenedStarRows

mutual
  /-- Whether checked lowering supplied positive, sibling-unique coordinates throughout
      the reopened tree. Over-limit coordinates remain valid input to this boundary. -/
  def ReopenedStarDomain.wellFormed : ReopenedStarDomain → Bool
    | .selectedLeaf => true
    | .repeatable _ rows => rows.wellFormed

  def ReopenedStarRows.wellFormed : ReopenedStarRows → Bool
    | .nil => true
    | .cons coordinate child rest =>
        !(coordinate == 0) && !rest.containsCoordinate coordinate &&
          child.wellFormed && rest.wellFormed
end

mutual
  /-- Whether declared capacity below the first star remains structurally open. -/
  def ReopenedStarDomain.hasOpenTail : ReopenedStarDomain → Bool
    | .selectedLeaf => false
    | .repeatable none _ => true
    | .repeatable (some repeatability) rows =>
        rows.length < repeatability || rows.hasOpenTail

  /-- Whether any actual child row contains an open reopened descendant. -/
  def ReopenedStarRows.hasOpenTail : ReopenedStarRows → Bool
    | .nil => false
    | .cons _ child rest => child.hasOpenTail || rest.hasOpenTail
end

namespace ReopenedStarDomain

/-- Bridge the hierarchical structural decision into the existing resolved operand
    boundary. Empty selected cells remain explicit cells and compose there. -/
def toResolvedSide (domain : ReopenedStarDomain)
    (cells : List (ValueListCell kind)) (hasHaving : Bool := false) :
    ResolvedValueListSide kind :=
  { cells
    hasUninstantiatedTail := domain.hasOpenTail
    hasHaving }

end ReopenedStarDomain

end A12Kernel
