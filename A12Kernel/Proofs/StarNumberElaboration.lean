import A12Kernel.Elaboration.StarNumber

namespace A12Kernel

/-- The concrete Number consumer retains the general checked path's exact model ancestry. -/
@[simp] theorem checkedStarNumberSource_ancestry (checked : CheckedStarNumberSource model) :
    checked.source.path.axes.map (·.level) =
      checked.source.declaration.repeatableScope :=
  checked.source.ancestryOwned

/-- Structural over-repetition replaces ordinary scalar findings at the checked cell boundary. -/
theorem checkedStarNumberSource_overLimit (checked : CheckedStarNumberSource model)
    (read : Env → FieldId → RawCell) (environment : Env)
    (overLimit : checked.environmentOverLimit environment = true) :
    (checked.checkedCell read environment).parsed = none ∧
      (checked.checkedCell read environment).findings = [.overRepetition] := by
  simp [CheckedStarNumberSource.checkedCell, overLimit]

end A12Kernel
