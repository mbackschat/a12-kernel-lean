import A12Kernel.Semantics.PartialDateInput

namespace A12Kernel

/-- Complete a selected, already-checked partial Date to its earliest day (spec/05, KF508).
The cell's own precision was enforced before selection; a mixed list's first declaration must
not reclassify the selected cell under a different precision. Unknown year remains non-relevant. -/
def firstFilledPartialDateResolution (format : FullDateTargetFormat) (text : String) :
    Option ValueAsDateResolution :=
  match classifyPartialDateStored format .yearOptional false text with
  | .admitted value => some (value.value.resolve .firstDay)
  | _ => none

end A12Kernel
