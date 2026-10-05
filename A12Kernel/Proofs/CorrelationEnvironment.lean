import A12Kernel.Semantics.Correlation

/-! Exact named-environment laws used by correlated-filter readers. -/

namespace A12Kernel

/-- Row zero is not a concrete repetition binding and cannot enter a correlated comparison. -/
@[simp]
theorem env_uniqueRowAt_zero (level : RepeatableLevel) :
    Env.uniqueRowAt? [(level, 0)] level = none := by
  simp [Env.uniqueRowAt?, Env.bindingAt, Except.toOption]

/-- Two distinct named levels in one complete environment retain their independent positive coordinates. -/
theorem env_crossLevel_bindings_resolve
    (outerLevel innerLevel : RepeatableLevel)
    (outerRow innerRow : RowIndex)
    (distinctLevels : outerLevel ≠ innerLevel)
    (outerPositive : outerRow ≠ 0)
    (innerPositive : innerRow ≠ 0) :
    Env.uniqueRowAt? [(outerLevel, outerRow), (innerLevel, innerRow)]
        outerLevel = some outerRow ∧
      Env.uniqueRowAt? [(outerLevel, outerRow), (innerLevel, innerRow)]
        innerLevel = some innerRow := by
  have reverseLevels : innerLevel ≠ outerLevel := Ne.symm distinctLevels
  simp [Env.uniqueRowAt?, Env.bindingAt, Except.toOption, distinctLevels,
    reverseLevels, outerPositive, innerPositive]

/-- Off-diagonal coordinates at distinct named levels cannot be represented by one scalar current-row value. -/
theorem env_offDiagonal_bindings_not_collapsible
    (outerLevel innerLevel : RepeatableLevel)
    (outerRow innerRow : RowIndex)
    (distinctLevels : outerLevel ≠ innerLevel)
    (distinctRows : outerRow ≠ innerRow)
    (outerPositive : outerRow ≠ 0)
    (innerPositive : innerRow ≠ 0) :
    ¬∃ row,
      Env.uniqueRowAt? [(outerLevel, outerRow), (innerLevel, innerRow)]
          outerLevel = some row ∧
        Env.uniqueRowAt? [(outerLevel, outerRow), (innerLevel, innerRow)]
          innerLevel = some row := by
  rcases env_crossLevel_bindings_resolve outerLevel innerLevel outerRow innerRow
    distinctLevels outerPositive innerPositive with
    ⟨outerResolved, innerResolved⟩
  have reverseRows : innerRow ≠ outerRow := Ne.symm distinctRows
  simp [outerResolved, innerResolved, reverseRows]

/-- A resolving correlation frame preserves an invalid named binding in its caller-owned structural channel. -/
theorem correlationFrame_rowAtResolving_error
    (frame : CorrelationFrame) (context : ResolvingCorrelationContext Error)
    (origin : HavingOrigin) (level : RepeatableLevel) (cause : EnvBindingError)
    (failed :
      (frame.envAt origin).bindingAt level =
        .error cause) :
    frame.rowAtResolving context { origin, source := .repeatable level } =
      .error (context.bindingError cause) := by
  simp [CorrelationFrame.rowAtResolving, failed, Except.mapError]

/-- A fixed group's own index does not read either environment; its ancestors constrain admission. -/
theorem fixed_repetition_reference_value (frame : CorrelationFrame)
    (context : ResolvingCorrelationContext Error) (origin : HavingOrigin) (path : List String) :
    frame.rowAt? { origin, source := .fixed path } = some 1 ∧
      frame.rowAtResolving context { origin, source := .fixed path } = .ok 1 := by
  exact ⟨rfl, rfl⟩

end A12Kernel
