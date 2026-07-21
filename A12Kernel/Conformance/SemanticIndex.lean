import A12Kernel.Semantics.SemanticIndex

/-! # Resolved literal-key semantic-index conformance

These cases separate validation's match-first policy from computation's column-strict policy. The input column is already normalized and checked: `entries` contains only uniquely resolvable keys, while `unavailableKey` records that at least one empty, duplicate, or malformed key was excluded.
-/

namespace A12Kernel

private def numberCell (amount : Rat) : CheckedCell :=
  { rawPresent := true, parsed := some (.num amount), findings := [] }

private def emptyCell : CheckedCell :=
  { rawPresent := false, parsed := none, findings := [] }

private def invalidNumberCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.declaredConstraint] }

private def requiredEmptyTarget : CheckedCell :=
  { rawPresent := false, parsed := none, findings := [.required] }

private def indexEntry (token : String) (target : CheckedCell) :
    ResolvedSemanticIndexEntry :=
  { token, target }

private def indexColumn (entries : List ResolvedSemanticIndexEntry)
    (unavailableKey : Option FormalCause := none) :
    ResolvedSemanticIndexColumn :=
  { entries, unavailableKey }

/- A unique validation match wins over an unrelated unavailable key; computation checks the column first. -/
example :
    let column := indexColumn
      [indexEntry "wanted" (numberCell 7)] (some .malformed)
    column.lookupValue .validation "wanted" = .value (.num 7) ∧
      column.lookupValue .computation "wanted" = .poison .malformed := by
  native_decide

/- Clean no-match and matched empty are the same phase-neutral empty observation. -/
example :
    let noMatch := indexColumn [indexEntry "other" (numberCell 7)]
    let matchedEmpty := indexColumn [indexEntry "wanted" emptyCell]
    noMatch.lookupValue .validation "wanted" = .empty ∧
      noMatch.lookupValue .computation "wanted" = .empty ∧
      matchedEmpty.lookupValue .validation "wanted" = .empty ∧
      matchedEmpty.lookupValue .computation "wanted" = .empty := by
  native_decide

/- The canonical validation consumer locks the externally observed contract: both forms of indexed emptiness compare equal to numeric zero and fire as OMISSION. -/
example :
    let noMatch := indexColumn [indexEntry "other" (numberCell 7)]
    let matchedEmpty := indexColumn [indexEntry "wanted" emptyCell]
    let number : NumField := { scale := 0, signed := false }
    NumericComparisonOp.equal.evalFixedRight
        (noMatch.validationNumberOperand number "wanted") 0 =
          .fired .omission ∧
      NumericComparisonOp.equal.evalFixedRight
        (matchedEmpty.validationNumberOperand number "wanted") 0 =
          .fired .omission := by
  native_decide

/- Without a clean match, an unavailable key makes validation unknown and computation poison. -/
example :
    let duplicateColumn := indexColumn [] (some .duplicateIndex)
    let emptyKeyColumn := indexColumn
      [indexEntry "other" (numberCell 7)] (some .required)
    duplicateColumn.lookupValue .validation "wanted" = .unknown .duplicateIndex ∧
      duplicateColumn.lookupValue .computation "wanted" = .poison .duplicateIndex ∧
      emptyKeyColumn.lookupValue .validation "wanted" = .unknown .required ∧
      emptyKeyColumn.lookupValue .computation "wanted" = .poison .required := by
  native_decide

/- A selected invalid target is phase-sensitive; the same invalidity in an unmatched row is not read. -/
example :
    let matched := indexColumn [indexEntry "wanted" invalidNumberCell]
    let unmatched := indexColumn [indexEntry "other" invalidNumberCell]
    let matchedAfterInvalid := indexColumn
      [indexEntry "other" invalidNumberCell,
        indexEntry "wanted" (numberCell 7)]
    matched.lookupValue .validation "wanted" = .unknown .declaredConstraint ∧
      matched.lookupValue .computation "wanted" = .poison .declaredConstraint ∧
      unmatched.lookupValue .validation "wanted" = .empty ∧
      unmatched.lookupValue .computation "wanted" = .empty ∧
      matchedAfterInvalid.lookupValue .validation "wanted" = .value (.num 7) ∧
      matchedAfterInvalid.lookupValue .computation "wanted" = .value (.num 7) := by
  native_decide

/- The same formal cause has a role-sensitive effect: an unavailable index key poisons the column, while computation ignores a required-only finding on the selected target. -/
example :
    let badKey := indexColumn [] (some .required)
    let requiredTarget := indexColumn
      [indexEntry "wanted" requiredEmptyTarget]
    badKey.lookupValue .computation "wanted" = .poison .required ∧
      requiredTarget.lookupValue .validation "wanted" = .unknown .required ∧
      requiredTarget.lookupValue .computation "wanted" = .empty := by
  native_decide

/- The empty Number consumer preserves signedness: equal no-match values can fire with different polarity. -/
example :
    let column := indexColumn [indexEntry "other" (numberCell 7)]
    let unsigned : NumField := { scale := 0, signed := false }
    let signed : NumField := { scale := 0, signed := true }
    NumericComparisonOp.greaterEqual.evalFixedRight
        (column.validationNumberOperand unsigned "wanted") 0 =
          .fired .value ∧
      NumericComparisonOp.greaterEqual.evalFixedRight
        (column.validationNumberOperand signed "wanted") 0 =
          .fired .omission := by
  native_decide

/- Presence consumes the resolved indexed observation rather than row existence. A clean match is filled, while a matched empty target and an absent row are both not filled. -/
example :
    let matched := indexColumn [indexEntry "wanted" (numberCell 7)]
    let matchedEmpty := indexColumn [indexEntry "wanted" emptyCell]
    let noMatch := indexColumn [indexEntry "other" (numberCell 7)]
    matched.validationFilled "wanted" = .fired .value ∧
      matched.validationNotFilled "wanted" = .notFired ∧
      matchedEmpty.validationFilled "wanted" = .notFired ∧
      matchedEmpty.validationNotFilled "wanted" = .fired .omission ∧
      noMatch.validationFilled "wanted" = .notFired ∧
      noMatch.validationNotFilled "wanted" = .fired .omission := by
  native_decide

/- Validation preserves the lookup policy at the presence consumer: a clean match wins over an unrelated unavailable key, while a selected invalid target and an unavailable no-match are unknown in both polarities. -/
example :
    let cleanMatch := indexColumn
      [indexEntry "wanted" (numberCell 7)] (some .malformed)
    let invalidMatch := indexColumn [indexEntry "wanted" invalidNumberCell]
    let unavailableNoMatch := indexColumn [] (some .duplicateIndex)
    cleanMatch.validationFilled "wanted" = .fired .value ∧
      cleanMatch.validationNotFilled "wanted" = .notFired ∧
      invalidMatch.validationFilled "wanted" = .unknown ∧
      invalidMatch.validationNotFilled "wanted" = .unknown ∧
      unavailableNoMatch.validationFilled "wanted" = .unknown ∧
      unavailableNoMatch.validationNotFilled "wanted" = .unknown := by
  native_decide

/- Computation presence inherits the column-first gate and the clean no-match-as-empty rule. -/
example :
    let matched := indexColumn [indexEntry "wanted" (numberCell 7)]
    let noMatch := indexColumn [indexEntry "other" (numberCell 7)]
    let invalidMatch := indexColumn [indexEntry "wanted" invalidNumberCell]
    let unavailableMatch := indexColumn
      [indexEntry "wanted" (numberCell 7)] (some .malformed)
    matched.computationFilled "wanted" = .holds ∧
      matched.computationNotFilled "wanted" = .notTrue ∧
      noMatch.computationFilled "wanted" = .notTrue ∧
      noMatch.computationNotFilled "wanted" = .holds ∧
      invalidMatch.computationFilled "wanted" = .poison .declaredConstraint ∧
      invalidMatch.computationNotFilled "wanted" = .poison .declaredConstraint ∧
      unavailableMatch.computationFilled "wanted" = .poison .malformed ∧
      unavailableMatch.computationNotFilled "wanted" = .poison .malformed := by
  native_decide

end A12Kernel
