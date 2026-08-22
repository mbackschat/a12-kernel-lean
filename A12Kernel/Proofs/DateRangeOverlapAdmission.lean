import A12Kernel.Elaboration.DateRangeOverlap

/-! # DateRange overlap admission laws

These laws characterize the Kernel's uniform-year gate over an authored overlap operand list.
They say when the gate cannot fire; they do not claim that the gate is the only refusal a list
can meet, nor anything about the compared values themselves. Resolved-endpoint overlap truth
remains in `A12Kernel.Proofs.DateRangeOverlap`.
-/

namespace A12Kernel

private theorem contains_eq_false_of_forall_ne {l : List Bool} {b : Bool}
    (h : ∀ x ∈ l, x ≠ b) : l.contains b = false := by
  simp only [List.contains, List.elem_eq_mem, decide_eq_false_iff_not]
  intro hMem
  exact h b hMem rfl

/-- A configured Base Year completes every yearless declaration, so no operand list mixes year
inclusion and the gate cannot fire in a configured model whatever the authored operands are. -/
theorem mixesDateRangeYearInclusion_eq_false_of_baseYear (model : FlatModel)
    (configured : model.baseYear.isSome = true)
    (operands : List (ResolvedFieldEntityOperand model)) :
    mixesDateRangeYearInclusion model operands = false := by
  have hFalse : ∀ value ∈ operands.filterMap (dateRangeOperandIncludesYear? model),
      value ≠ false := by
    intro value hValue
    rw [List.mem_filterMap] at hValue
    obtain ⟨operand, _, hOperand⟩ := hValue
    cases operand with
    | field declaration form =>
        cases form <;> simp_all [dateRangeOperandIncludesYear?]
    | _ => simp_all [dateRangeOperandIncludesYear?]
  simp only [mixesDateRangeYearInclusion,
    contains_eq_false_of_forall_ne hFalse, Bool.and_false]

/-- A uniformly yearless list never mixes either, which is what lets the unconfigured yearless
route own that shape without contradicting this gate. -/
theorem mixesDateRangeYearInclusion_eq_false_of_no_year (model : FlatModel)
    (operands : List (ResolvedFieldEntityOperand model))
    (yearless : ∀ operand ∈ operands,
      dateRangeOperandIncludesYear? model operand ≠ some true) :
    mixesDateRangeYearInclusion model operands = false := by
  have hTrue : ∀ value ∈ operands.filterMap (dateRangeOperandIncludesYear? model),
      value ≠ true := by
    intro value hValue
    rw [List.mem_filterMap] at hValue
    obtain ⟨operand, hMember, hOperand⟩ := hValue
    intro hEq
    exact yearless operand hMember (hEq ▸ hOperand)
  simp only [mixesDateRangeYearInclusion,
    contains_eq_false_of_forall_ne hTrue, Bool.false_and]

end A12Kernel
