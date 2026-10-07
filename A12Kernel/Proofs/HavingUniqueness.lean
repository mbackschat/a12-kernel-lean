import A12Kernel.Semantics.HavingUniqueness

namespace A12Kernel.HavingUniqueness

/-- A duplicate closes either phase before any later read, including a structural failure. -/
theorem havingUniquenessScan_deciding_prefix (phase : Phase) (read : Operand → Except Error (ValueListCell kind))
    (first : Operand) (rest : List Operand) (seen : List (ValueListAtom kind)) (value : ValueListAtom kind)
    (readFirst : read first = .ok (.present value))
    (duplicate : seen.any (ValueListAtom.equal value) = true) :
    scan phase read seen (first :: rest) = .ok .holds := by
  cases phase <;> simp [scan, readFirst, ValueListCell.duplicateComputationStep, duplicate,
    bind, Except.bind, pure, Except.pure]

/-- Validation skips a reached invalid operand without changing the duplicate accumulator. -/
theorem havingUniquenessScan_validation_skip_invalid (read : Operand → Except Error (ValueListCell kind))
    (first : Operand) (rest : List Operand) (seen : List (ValueListAtom kind)) (cause : FormalCause)
    (readFirst : read first = .ok (.unknown cause)) :
    scan .validation read seen (first :: rest) = scan .validation read seen rest := by
  simp [scan, readFirst, ValueListCell.duplicateComputationStep, bind, Except.bind]

/-- The same invalid prefix is terminal in computation, independently of later duplicates. -/
theorem havingUniquenessScan_computation_poison (read : Operand → Except Error (ValueListCell kind))
    (first : Operand) (rest : List Operand) (seen : List (ValueListAtom kind)) (cause : FormalCause)
    (readFirst : read first = .ok (.unknown cause)) :
    scan .computation read seen (first :: rest) = .ok (.poison cause) := by
  simp [scan, readFirst, ValueListCell.duplicateComputationStep, bind, Except.bind, pure, Except.pure]

end A12Kernel.HavingUniqueness
