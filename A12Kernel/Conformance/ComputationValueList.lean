import A12Kernel.Proofs.ComputationValueList

namespace A12Kernel.Conformance.ComputationValueList

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def side (cells : List (ValueListCell .token)) : ResolvedValueListSide .token :=
  { cells, hasUninstantiatedTail := false, hasHaving := false }

private def evaluate (op : ValueListQuantifier) (fields values : List (ValueListCell .token)) :=
  op.evalComputation [side fields] [side values]

example : evaluate .atLeastOne [.present "x", .unknown .malformed] [.present "x"] = .holds ∧
    evaluate .atLeastOne [.unknown .malformed, .present "x"] [.present "x"] = .poison .malformed ∧
    evaluate .atLeastOne [.unknown .malformed] [] = .notTrue := by decide

example : evaluate .no [.present "x", .unknown .malformed] [.present "x"] = .notTrue ∧
    evaluate .no [.present "x"] [.present "x", .unknown .declaredConstraint] = .poison .declaredConstraint := by decide

example : evaluate .notAll [.empty] [.unknown .malformed] = .notTrue ∧
    evaluate .notAll [.present "x", .unknown .malformed] [.present "y"] = .holds ∧
    evaluate .notAll [.present "x", .unknown .malformed] [.present "x"] = .poison .malformed := by decide

example : evaluate .notAll [.unknown .malformed, .present "x"] [.unknown .declaredConstraint] =
    .poison .malformed ∧
    evaluate .notAll [.present "x", .unknown .malformed] [.unknown .declaredConstraint] =
      .poison .declaredConstraint := by decide

private def resolve (bad : Bool) : Except String (ResolvedValueListSide .token) :=
  if bad then .error "address" else .ok (side [.present "x"])

example : ValueListQuantifier.atLeastOne.evalComputationWith resolve resolve [false, true] [false] =
    .ok .holds := by decide

example : ValueListQuantifier.atLeastOne.evalComputationWith resolve resolve [true] [] =
    .ok .notTrue := by decide

/-- The scalar pair evaluates members and subject even where plural prepasses skip one side. -/
example : ValueListMembershipOp.included.evalComputation [side [.unknown .malformed]] [side [.empty]] =
    .poison .malformed ∧
    ValueListMembershipOp.notIncluded.evalComputation [side [.empty]] [side [.unknown .declaredConstraint]] =
    .poison .declaredConstraint := by decide

example : [ValueListMembershipOp.included, .notIncluded].all (fun op =>
    op.evalComputation [side [.empty]] [side [.present "x"]] == .notTrue) := by decide

end A12Kernel.Conformance.ComputationValueList
