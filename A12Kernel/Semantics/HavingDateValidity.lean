import A12Kernel.Semantics.CorrelationContext
import A12Kernel.Semantics.ConstructedDateInputs

namespace A12Kernel

/-- A direct Date component retains its own capture origin and maps host failures at the
correlated-read boundary (spec/05 §3 and spec/07 §3). -/
def readHavingDateComponent (origin : HavingOrigin) (source : ResolvedConstructedDateSource)
    (phase : Phase) (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error CheckedConstructedDateComponent :=
  source.readWith phase (context.read (frame.envAt origin))
    (context.storedText (frame.envAt origin)) context.world (fun result => result.mapError fun
      | .stringNotConvertible _ _ => context.temporalValueFailure
      | .dateYearStoredMissing field => context.storedTextUnavailable field
      | .todayWorldRequired | .nowWorldRequired => context.worldUnavailable
      | _ => context.unsupportedDateCalendar)

end A12Kernel
