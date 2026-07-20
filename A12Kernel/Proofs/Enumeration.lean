import A12Kernel.Semantics.Enumeration

/-! # Resolved Enumeration/category comparison laws -/

namespace A12Kernel

/-- The category token aligned with a matching head stored token is selected directly. -/
theorem enumerationCategory_lookup_head
    (storedToken categoryToken : String)
    (storedRemaining categoryRemaining : List String)
    (categoryNonempty : categoryToken.isEmpty = false) :
  ({ storedTokens := storedToken :: storedRemaining
     categoryTokens := categoryToken :: categoryRemaining } :
      ResolvedEnumerationCategory).categoryTokenFor? storedToken =
        some categoryToken := by
  simp [ResolvedEnumerationCategory.categoryTokenFor?,
    ResolvedEnumerationCategory.lookupAligned?, categoryNonempty]

/-- A nonmatching positional pair is skipped by advancing both vectors together without changing their alignment. -/
theorem enumerationCategory_lookup_skip
    (requested storedToken categoryToken : String)
    (storedRemaining categoryRemaining : List String)
    (notMatch : (storedToken == requested) = false) :
    ({ storedTokens := storedToken :: storedRemaining
       categoryTokens := categoryToken :: categoryRemaining } :
      ResolvedEnumerationCategory).categoryTokenFor? requested =
    ({ storedTokens := storedRemaining
       categoryTokens := categoryRemaining } :
      ResolvedEnumerationCategory).categoryTokenFor? requested := by
  simp [ResolvedEnumerationCategory.categoryTokenFor?,
    ResolvedEnumerationCategory.lookupAligned?, notMatch]

/-- Direct Enumeration projection exposes the exact nonempty stored token, not display text. -/
theorem enumeration_stored_resolves_exactly
    (storedToken : String) (nonempty : storedToken.isEmpty = false) :
    ResolvedEnumerationProjection.stored.resolveOperand
        (.value (.enum storedToken)) =
      .value storedToken true := by
  simp [ResolvedEnumerationProjection.resolveOperand,
    ResolvedEnumerationProjection.tokenFor?, nonempty]

/-- A successful category lookup exposes exactly the mapped category token. -/
theorem enumeration_category_resolves_lookup
    (mapping : ResolvedEnumerationCategory)
    (storedToken categoryToken : String)
    (storedNonempty : storedToken.isEmpty = false)
    (lookup : mapping.categoryTokenFor? storedToken = some categoryToken) :
    (ResolvedEnumerationProjection.category mapping).resolveOperand
        (.value (.enum storedToken)) =
      .value categoryToken true := by
  simp [ResolvedEnumerationProjection.resolveOperand,
    ResolvedEnumerationProjection.tokenFor?, storedNonempty, lookup]

/-- Two stored tokens mapped to the same category token have the same literal-comparison verdict. -/
theorem enumerationCategory_manyToOne_sameVerdict
    (mapping : ResolvedEnumerationCategory)
    (leftStored rightStored categoryToken expected : String)
    (op : EqualityOp)
    (leftNonempty : leftStored.isEmpty = false)
    (rightNonempty : rightStored.isEmpty = false)
    (leftLookup : mapping.categoryTokenFor? leftStored = some categoryToken)
    (rightLookup : mapping.categoryTokenFor? rightStored = some categoryToken) :
    (ResolvedEnumerationProjection.category mapping).evalLiteral
        op (.value (.enum leftStored)) expected =
      (ResolvedEnumerationProjection.category mapping).evalLiteral
        op (.value (.enum rightStored)) expected := by
  simp [ResolvedEnumerationProjection.evalLiteral,
    enumeration_category_resolves_lookup mapping leftStored categoryToken
      leftNonempty leftLookup,
    enumeration_category_resolves_lookup mapping rightStored categoryToken
      rightNonempty rightLookup]

/-- Empty Enumeration input is not evaluated under either equality operator or projection. -/
theorem enumeration_empty_notFired
    (projection : ResolvedEnumerationProjection)
    (op : EqualityOp) (expected : String) :
    projection.evalLiteral op .empty expected = .notFired := by
  rfl

/-- Formal unavailability is retained as UNKNOWN rather than converted to an ordinary mismatch. -/
theorem enumeration_unavailable_unknown
    (projection : ResolvedEnumerationProjection)
    (op : EqualityOp) (cause : FormalCause) (expected : String) :
    projection.evalLiteral op (.unknown cause) expected = .unknown := by
  rfl

/-- A successfully resolved Enumeration/category token cannot produce OMISSION because the operand is present and fixed. Together with the empty and unavailable laws, this covers every admitted observation. -/
theorem enumeration_resolved_never_omission
    (projection : ResolvedEnumerationProjection)
    (op : EqualityOp) (observation : CellObservation)
    (actual expected : String)
    (resolved : projection.resolveOperand observation = .value actual true) :
    projection.evalLiteral op observation expected ≠ .fired .omission := by
  rw [ResolvedEnumerationProjection.evalLiteral, resolved]
  cases op <;> simp [EqualityOp.evalSimple] <;> split <;> simp

end A12Kernel
