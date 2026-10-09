import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.CustomFieldValidity

namespace A12Kernel

/-- Empty and formally unavailable inputs do not consult the host registry. A missing evaluation
World differs from an available World whose registry has no entry (spec/06 A.3). -/
private def validityForObservation (name : String) (observation : CellObservation String)
    (context : ResolvingCorrelationContext Error) : Except Error CheckedCustomFieldValidity := do
  match observation with
  | .value value =>
      if value.isEmpty then return { name, validator? := none }
      let some world := context.world | throw context.worldUnavailable
      pure { name, validator? := world.resolveCustomFieldValidator? name }
  | _ => pure { name, validator? := none }

def evalHavingTypeValidityValidation (operation : CustomFieldValidityOp)
    (reference : HavingPresenceRef) (name : String)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let observation := (← reference.observeInAtResolving .validation context frame).asTypeValidityText
  let validity ← validityForObservation name observation context
  (validity.evalValidation operation observation).mapError fun _ => context.typeValidityValueFailure

def evalHavingTypeValidityComputation (operation : CustomFieldValidityOp)
    (reference : HavingPresenceRef) (name : String)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult := do
  let observation := (← reference.observeInAtResolving .computation context frame).asTypeValidityText
  let validity ← validityForObservation name observation context
  match validity.evalComputation operation observation with
  | .holds => pure .holds
  | .notTrue => pure .notTrue
  | .poison cause => pure (.poison cause)
  | .validatorUnavailable => throw context.typeValidityValueFailure

end A12Kernel
