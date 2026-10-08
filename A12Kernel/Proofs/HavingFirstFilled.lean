import A12Kernel.Semantics.HavingFirstFilled

namespace A12Kernel

/-- A terminal direct prefix prevents every suffix read and extent acquisition. This specializes
the shared continuation scan without assuming that the suffix is well formed or readable. -/
theorem havingFirstFilled_direct_terminal
    (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (step : FirstFilledScanState → Ref → CheckedCell → FirstFilledScanState ⊕ Result)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (reference : Ref) (cell : CheckedCell) (result : Result)
    (suffix : List (HavingFieldListSlot Ref))
    (read : context.read (frame.envAt (origin reference)) (field reference) = .ok cell)
    (terminal : step {} reference cell = .inr result) :
    HavingFirstFilled.scanWith origin field step context frame (.direct reference :: suffix) = .ok (.inr result) := by
  simp [HavingFirstFilled.scanWith, HavingFieldListSlot.foldRead, read, terminal,
    bind, Except.bind, pure, Except.pure]

end A12Kernel
