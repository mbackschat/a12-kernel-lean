import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.ConstructedDateInputs

namespace A12Kernel

/-- Each component owns its candidate/captured origin; the constructor retains authored order
and its selected calendar profile (spec/05 §3 and spec/07 §3). -/
abbrev HavingDateComponents := ResolvedConstructedDateComponents (HavingOrigin × ResolvedConstructedDateSource)

namespace HavingDateComponents

def references (source : HavingDateComponents) : List HavingPresenceRef :=
  source.sources.filterMap fun (origin, component) =>
    component.fieldId?.map fun field => { origin, field }

def evaluate (source : HavingDateComponents) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ConstructedDateObservation := do
  let read (operand : HavingOrigin × ResolvedConstructedDateSource) :=
    operand.2.readWith phase (context.read (frame.envAt operand.1))
      (context.storedText (frame.envAt operand.1)) context.world (fun result => result.mapError fun
        | .stringNotConvertible _ _ => context.temporalValueFailure
        | .dateYearStoredMissing field => context.storedTextUnavailable field
        | .todayWorldRequired | .nowWorldRequired => context.worldUnavailable
        | _ => context.unsupportedDateCalendar)
  pure (source.applyProfileReality (← source.evaluateComponentsWith read phase))

def evalValidationRead (source : HavingDateComponents) (operation : ConstructedDateValidityOp)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  pure ((← source.evaluate .validation context frame).validityVerdict operation |>.toOption.getD .unknown)

def evalComputationRead (source : HavingDateComponents) (operation : ConstructedDateValidityOp)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error ComputationConditionResult := do
  pure (match (← source.evaluate .computation context frame).validityVerdict operation with
    | .error cause => .poison cause
    | .ok (.fired _) => .holds
    | .ok _ => .notTrue)

end HavingDateComponents
end A12Kernel
