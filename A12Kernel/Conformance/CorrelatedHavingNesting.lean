import A12Kernel.Semantics.Correlation

/-! # Filter connective-bracketing conformance locks

A `Having` condition reuses the shared connective tree, so its bracketing is not a filter-local
account. What needs locking is that the tree's **shape** decides which rows survive: for each
authored nesting, the wrong flattenings a consumer reaches for are asserted here beside the correct
reading rather than left implicit. Split out of the correlation-selection locks, which own the
captured-environment semantics; this module keeps its own field and row fixtures because the two
families share no invariant.
-/

namespace A12Kernel.Conformance.CorrelatedHavingNesting

open A12Kernel

private def items : RepeatableLevel := 10

private def count : FlatNumberField :=
  { id := 0, info := { scale := 0, signed := false } }

private def payload : FlatNumberField :=
  { id := 1, info := { scale := 0, signed := false } }

private def marker : FlatNumberField :=
  { id := 2, info := { scale := 0, signed := false } }

private def checkedNumber : RawCell → CheckedCell :=
  formalCheck { kind := .number count.info }

private def number (value : Rat) : RawCell :=
  .parsed (.num value)

/- A bracketed `Or` **nested under** `And`, which also mixes leaf kinds inside the disjunction. The
   two flattenings are the wrong accounts a consumer reaches for, and each is locked here rather
   than merely asserted: treating the tree as one conjunction of three leaves keeps nothing, and as
   one disjunction keeps every row. Kernel-retained at the same count of two. -/

private def nestedRow (index : RowIndex) : Env :=
  [(items, index)]

private def nestedText (value : String) : CheckedCell :=
  { rawPresent := true, parsed := some (.str value), findings := [] }

private def nestedAbsentText : CheckedCell :=
  { rawPresent := false, parsed := none, findings := [] }

/-- Per row: is the Number operand filled, is the String operand filled, and what the third
    operand's text is. Row 3 satisfies neither disjunct and row 4 fails the conjunct. -/
private def nestedSpec : RowIndex → Bool × Bool × String
  | 1 => (true, true, "X")
  | 2 => (true, false, "K")
  | 3 => (true, false, "X")
  | _ => (false, true, "K")

private def nestedContext : CorrelationContext where
  read environment field :=
    let row := match environment with
      | [(_, index)] => index
      | _ => 0
    let (numberFilled, textFilled, tag) := nestedSpec row
    if field == count.id then
      checkedNumber (if numberFilled then number 7 else .empty)
    else if field == payload.id then
      (if textFilled then nestedText "s" else nestedAbsentText)
    else
      nestedText tag

private def nestedLeaves : CorrelatedHaving :=
  .and
    (CorrelatedHaving.presence .filled { origin := .inner, field := count.id })
    (.or
      (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })
      (CorrelatedHaving.compareStringLiteral .equal
        { origin := .inner, field := { id := marker.id } } "K"))

private def flattenedToConjunction : CorrelatedHaving :=
  .and
    (CorrelatedHaving.presence .filled { origin := .inner, field := count.id })
    (.and
      (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })
      (CorrelatedHaving.compareStringLiteral .equal
        { origin := .inner, field := { id := marker.id } } "K"))

private def flattenedToDisjunction : CorrelatedHaving :=
  .or
    (CorrelatedHaving.presence .filled { origin := .inner, field := count.id })
    (.or
      (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })
      (CorrelatedHaving.compareStringLiteral .equal
        { origin := .inner, field := { id := marker.id } } "K"))

private def nestedCandidates : List Env :=
  (List.range 4).map fun index => nestedRow (index + 1)

example :
    nestedLeaves.selectEnvironments nestedContext [] nestedCandidates
      = [nestedRow 1, nestedRow 2] := by
  native_decide

example :
    (flattenedToConjunction.selectEnvironments nestedContext [] nestedCandidates).length = 0 ∧
      (flattenedToDisjunction.selectEnvironments nestedContext [] nestedCandidates).length = 4 := by
  native_decide

/-- Three-level nesting, `A And (B Or (C And notA))`, where the innermost conjunct contradicts the
outer one. Built from the same three leaves plus the negative presence polarity so the fixtures stay
shared. -/
private def threeLevelNesting : CorrelatedHaving :=
  .and
    (CorrelatedHaving.presence .filled { origin := .inner, field := count.id })
    (.or
      (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })
      (.and
        (CorrelatedHaving.compareStringLiteral .equal
          { origin := .inner, field := { id := marker.id } } "K")
        (CorrelatedHaving.presence .notFilled { origin := .inner, field := count.id })))

/-- The leftward-associated misreading of the shape above: `(A And B) Or (C And notA)`. -/
private def threeLevelLeftAssociated : CorrelatedHaving :=
  .or
    (.and
      (CorrelatedHaving.presence .filled { origin := .inner, field := count.id })
      (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id }))
    (.and
      (CorrelatedHaving.compareStringLiteral .equal
        { origin := .inner, field := { id := marker.id } } "K")
      (CorrelatedHaving.presence .notFilled { origin := .inner, field := count.id }))

/- **Bracketing is honoured at three levels, and the depth is what the ladder separates.** The
innermost conjunct can never hold where the outermost does, so the correct reading collapses to
`A And B` and keeps row 1 alone; associating the outer `And` leftward keeps row 4 as well. Measured
against the Kernel at a12-dmkits `eded8263` on the analogous arithmetic shape, where a `Sum` ladder
over four rows fires only the correct rung while both flattening rungs stay silent. -/
example :
    threeLevelNesting.selectEnvironments nestedContext [] nestedCandidates
        = [nestedRow 1] ∧
      threeLevelLeftAssociated.selectEnvironments nestedContext [] nestedCandidates
        = [nestedRow 1, nestedRow 4] := by
  native_decide

end A12Kernel.Conformance.CorrelatedHavingNesting
