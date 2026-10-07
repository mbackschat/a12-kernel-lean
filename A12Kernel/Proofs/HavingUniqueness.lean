import A12Kernel.Semantics.HavingUniqueness

namespace A12Kernel.HavingFieldListSlot

/-- A terminal direct step leaves every later slot's acquisition and reads unused. -/
theorem foldRead_deciding_direct {Ref Error Accumulator Result : Type}
    (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (step : Accumulator → Ref → Env → Except Error (Sum Accumulator Result))
    (accumulator : Accumulator) (first : Ref) (rest : List (HavingFieldListSlot Ref))
    (result : Result)
    (decides : step accumulator first (frame.envAt (origin first)) = .ok (.inr result))
    (onOmitted : Accumulator → Ref → Except Error (Sum Accumulator Result) := fun next _ => pure (.inl next)) :
    foldRead origin field context frame step accumulator (.direct first :: rest) onOmitted = .ok (.inr result) := by
  simp [foldRead, decides, bind, Except.bind, pure, Except.pure]

end A12Kernel.HavingFieldListSlot

namespace A12Kernel.HavingUniqueness

/-- A duplicate closes either phase before any later read, including a structural failure. -/
theorem havingUniquenessScan_deciding_prefix (phase : Phase) (read : Operand → Except Error (ValueListCell kind))
    (first : Operand) (rest : List Operand) (seen : List (ValueListAtom kind)) (value : ValueListAtom kind)
    (readFirst : read first = .ok (.present value))
    (duplicate : seen.any (ValueListAtom.equal value) = true) :
    scan phase read seen (first :: rest) = .ok .holds := by
  cases phase <;> simp [scan, step, readFirst, ValueListCell.duplicateComputationStep, duplicate,
    bind, Except.bind, pure, Except.pure]

/-- Validation skips a reached invalid operand without changing the duplicate accumulator. -/
theorem havingUniquenessScan_validation_skip_invalid (read : Operand → Except Error (ValueListCell kind))
    (first : Operand) (rest : List Operand) (seen : List (ValueListAtom kind)) (cause : FormalCause)
    (readFirst : read first = .ok (.unknown cause)) :
    scan .validation read seen (first :: rest) = scan .validation read seen rest := by
  simp [scan, step, readFirst, ValueListCell.duplicateComputationStep, bind, Except.bind]

/-- The same invalid prefix is terminal in computation, independently of later duplicates. -/
theorem havingUniquenessScan_computation_poison (read : Operand → Except Error (ValueListCell kind))
    (first : Operand) (rest : List Operand) (seen : List (ValueListAtom kind)) (cause : FormalCause)
    (readFirst : read first = .ok (.unknown cause)) :
    scan .computation read seen (first :: rest) = .ok (.poison cause) := by
  simp [scan, step, readFirst, ValueListCell.duplicateComputationStep, bind, Except.bind, pure, Except.pure]

end A12Kernel.HavingUniqueness
