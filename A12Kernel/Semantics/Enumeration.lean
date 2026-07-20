import A12Kernel.Semantics.ScalarEquality

/-! # Resolved Enumeration and category comparison

This capsule begins after ordinary closed-Enumeration declaration checks, validation-phase cell observation, category-name selection, and literal-domain admission. One selected category retains the declaration-order stored-token and category-token vectors. Their aligned positions define the category projection; repeated category tokens are legal and provide the intended many-to-one mapping.

The admitted caller supplies unique nonempty stored tokens, one nonempty category token per stored token, a clean stored token from that domain, and a nonempty comparison literal from the selected projection's domain. Total fallback for incoherent vectors, missing tokens, or empty mapped tokens is an internal fail-closed refinement without a legal-kernel correspondence claim.
-/

namespace A12Kernel

/-- One already-selected category represented exactly as the two parallel declaration-order vectors. -/
structure ResolvedEnumerationCategory where
  storedTokens : List String
  categoryTokens : List String
  deriving Repr, DecidableEq

namespace ResolvedEnumerationCategory

/-- Pair two declaration-order vectors while searching for one stored token. This is the executable positional relation used by `categoryTokenFor?`. -/
def lookupAligned? (requested : String) :
    List String → List String → Option String
  | stored :: storedRemaining, mapped :: mappedRemaining =>
      if stored == requested then
        if mapped.isEmpty then none else some mapped
      else
        lookupAligned? requested storedRemaining mappedRemaining
  | _, _ => none

/-- Lockstep positional lookup. Duplicate category tokens are retained; unique stored tokens and equal vector lengths are preceding obligations. -/
def categoryTokenFor? (category : ResolvedEnumerationCategory)
    (requested : String) : Option String :=
  lookupAligned? requested category.storedTokens category.categoryTokens

end ResolvedEnumerationCategory

/-- The two resolved runtime projections admitted by this capsule: the stored Enumeration token itself or one selected positional category. -/
inductive ResolvedEnumerationProjection where
  | stored
  | category (mapping : ResolvedEnumerationCategory)
  deriving Repr, DecidableEq

namespace ResolvedEnumerationProjection

/-- Resolve a clean stored token through the selected projection. Empty/missing results are defensive failures outside the admitted legal-model boundary. -/
def tokenFor? (projection : ResolvedEnumerationProjection)
    (stored : String) : Option String :=
  if stored.isEmpty then
    none
  else
    match projection with
    | .stored => some stored
    | .category mapping => mapping.categoryTokenFor? stored

/-- Classify one validation-phase Enumeration observation for exact token comparison. Empty remains not evaluated; a wrong value kind or incoherent projection fails closed as malformed. -/
def resolveOperand (projection : ResolvedEnumerationProjection) :
    CellObservation → SimpleComparisonOperand String
  | .empty => .notEvaluated
  | .value (.enum storedToken) =>
      match projection.tokenFor? storedToken with
      | some projected => .value projected true
      | none => .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Compare one resolved Enumeration or category token with an already-admitted literal. Every firing is VALUE because only a clean filled Enumeration can reach a value comparison. -/
def evalLiteral (projection : ResolvedEnumerationProjection)
    (op : EqualityOp) (observation : CellObservation)
    (expected : String) : Verdict :=
  op.evalSimple (· == ·) (projection.resolveOperand observation) expected

end ResolvedEnumerationProjection

end A12Kernel
