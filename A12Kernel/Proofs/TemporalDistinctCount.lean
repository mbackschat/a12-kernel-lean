import A12Kernel.Elaboration.TemporalDistinctCount
import A12Kernel.Proofs.ValueList

/-! # Checked temporal distinct-count laws

The one law this fold owes beyond its examples: the identity it compares is a function of the
operand's **declared component set** and the model's Base Year, and not of the components that set
omits.

That is worth a theorem rather than more cases because of where the omitted components come from.
`RawCell.parsed` carries whatever value the classifier that admitted the stored text produced, and
the document's coherence check re-derives boolean, confirm and DateRange values from their stored
text but not temporal ones — so for a `yyyy-MM` declaration nothing pins which day the producer
chose. A count that varied with that choice would not be a semantics, and no same-producer example
can rule it out. The congruence below rules it out for every cell pair at once.
-/

namespace A12Kernel

/-- Two decoded values that agree on every component the declared set **names** compare as one
    value, whatever they hold in the components it omits.

    Stated as a congruence rather than as "the omitted field is ignored" because that is the form a
    consumer needs: it says exactly which agreements a producer must reproduce to reproduce the
    count, and it is silent about the rest. -/
theorem maskedDateComponents_congr
    (components : TemporalComponents) (baseYear : Option Int) (left right : DateParts)
    (yearAgrees : components.year = true → left.year = right.year)
    (monthAgrees : components.month = true → left.month = right.month)
    (dayAgrees : components.day = true → left.day = right.day) :
    maskedDateComponents components baseYear left
      = maskedDateComponents components baseYear right := by
  unfold maskedDateComponents
  cases hYear : components.year <;> cases hMonth : components.month <;>
    cases hDay : components.day <;>
    simp [hYear, hMonth, hDay, yearAgrees, monthAgrees, dayAgrees]

/-- The complete calendar date is the one set that constrains all three components, so there the
    congruence degenerates to equality of the decoded parts. Recorded as the boundary case: it is
    what makes the theorem above a widening of the old complete-date-only fold rather than a
    different rule. -/
theorem maskedDateComponents_fullDate_injective
    (baseYear : Option Int) (left right : DateParts)
    (agree : maskedDateComponents TemporalComponents.fullDate baseYear left
      = maskedDateComponents TemporalComponents.fullDate baseYear right) :
    left.year = right.year ∧ left.month = right.month ∧ left.day = right.day := by
  unfold maskedDateComponents TemporalComponents.fullDate at agree
  simp at agree
  exact ⟨agree.1, agree.2.1, agree.2.2⟩

end A12Kernel
