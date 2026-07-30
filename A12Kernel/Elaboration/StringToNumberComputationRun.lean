import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StringComputationRunResult

/-! # One checked String-to-Number computation run

This capsule executes exactly one checked String table followed by one checked scalar Number table that converts the String target through `FieldValueAsNumber`. The String outcome remains typed and complete; only the Number consumer receives the String target's checked dependency cell through the existing scalar read boundary. The result retains each family's established projection instead of erasing them into a common outcome type.

Repeatable activation, additional families, a generic dependency graph, and whole-document application remain separate.
-/

namespace A12Kernel

namespace CheckedNumericComputationAtom

/-- Whether this is the exact String-to-Number conversion leaf for one field. Other numeric reads and guard-only references do not satisfy the bounded composition gate. -/
def isFieldValueAsNumberOf (field : FieldId) :
    CheckedNumericComputationAtom model → Bool
  | .numeric (.fieldValueAsNumber source) => source.fieldId == field
  | _ => false

end CheckedNumericComputationAtom

namespace CheckedNumericComputationTable

/-- Whether any Number row contains the exact `FieldValueAsNumber` consumer leaf. -/
def consumesStringAsNumber
    (table : CheckedNumericComputationTable model)
    (field : FieldId) : Bool :=
  table.selectableAlternatives.any fun alternative =>
    alternative.operation.operation.core.expression.anyAtom
      (CheckedNumericComputationAtom.isFieldValueAsNumberOf field)

end CheckedNumericComputationTable

inductive StringToNumberComputationRunPlanError where
  | stringReadsNumber (stringTarget numberTarget : FieldId)
  | numberRequiresRepeatableContext (target : FieldId)
  | numberDoesNotConsumeStringAsNumber
      (numberTarget stringTarget : FieldId)
  deriving Repr, DecidableEq

/-- One statically ordered heterogeneous run whose Number consumer is known to convert its scalar String producer. -/
structure CheckedStringToNumberComputationRun (model : FlatModel) where
  string : CheckedStringComputationTable model
  number : CheckedNumericComputationTable model
  stringDoesNotReadNumber :
    string.referencesField number.targetField = false
  numberScalar : number.supportsScalarEvaluation = true
  numberConsumesStringAsNumber :
    number.consumesStringAsNumber string.targetField = true

/-- Certify the exact two-family dependency edge without constructing a general schedule. -/
def certifyStringToNumberComputationRun
    (string : CheckedStringComputationTable model)
    (number : CheckedNumericComputationTable model) :
    Except StringToNumberComputationRunPlanError
      (CheckedStringToNumberComputationRun model) :=
  if hReverse : string.referencesField number.targetField = false then
    if hScalar : number.supportsScalarEvaluation = true then
      if hForward :
          number.consumesStringAsNumber string.targetField = true then
        .ok {
          string
          number
          stringDoesNotReadNumber := hReverse
          numberScalar := hScalar
          numberConsumesStringAsNumber := hForward
        }
      else
        .error (.numberDoesNotConsumeStringAsNumber
          number.targetField string.targetField)
    else
      .error (.numberRequiresRepeatableContext number.targetField)
  else
    .error (.stringReadsNumber string.targetField number.targetField)

/-- Exact rich outcomes from the two family owners. Field IDs remain attached so result projection cannot lose family or target identity. -/
structure StringToNumberComputationOutcomes where
  string : FieldId × StringTargetOutcome
  number : FieldId × NumericTargetOutcome
  deriving Repr, DecidableEq

inductive StringToNumberComputationRunFault where
  | string (cause : StringComputationRunFault)
  | number (cause : NumericComputationRunFault)
  deriving Repr, DecidableEq

namespace CheckedStringToNumberComputationRun

/-- Overlay exactly the completed String target on the Number scalar context. -/
def numberContextWithString
    (run : CheckedStringToNumberComputationRun model)
    (world : World)
    (input : CheckedDocument model)
    (string : StringComputationRunCompletion) :
    ScalarComputationContext :=
  StringComputationContext.withDependencyCell
    (input.scalarComputationContext world)
    run.string.targetField string.dependencyCell

/-- Execute the String producer against the immutable document, overlay only its completed dependency observation, and evaluate the reached Number consumer. -/
def execute (run : CheckedStringToNumberComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except StringToNumberComputationRunFault
      StringToNumberComputationOutcomes :=
  match run.string.evaluateCompletion patterns
      input.stringComputationContext with
  | .error cause => .error (.string cause)
  | .ok string =>
      match run.number.evaluateCompletion
          (run.numberContextWithString world input string) with
      | .error cause => .error (.number cause)
      | .ok number => .ok {
          string := (string.targetField, string.outcome)
          number := (number.targetField, number.outcome)
        }

end CheckedStringToNumberComputationRun

/-- Family-preserving public result for the bounded heterogeneous run. -/
structure StringToNumberComputationRunView
    (StringResidual NumberPayload : Type) where
  string : StringComputationRunView StringResidual
  number :
    NumericComputationRunView (ComputationFormalMessage NumberPayload)
  deriving Repr, DecidableEq

inductive StringToNumberComputationRunResultFault where
  | execution (cause : StringToNumberComputationRunFault)
  | numberSource (cause : NumericSourceTargetError)
  deriving Repr, DecidableEq

namespace CheckedStringToNumberComputationRun

/-- Project each rich outcome through its existing family owner while retaining the two result channels separately. -/
def executeResult (run : CheckedStringToNumberComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual) :
    Except StringToNumberComputationRunResultFault
      (StringToNumberComputationRunView StringResidual NumberPayload) := do
  let outcomes ← (run.execute world patterns input).mapError .execution
  let string :=
    StringComputationRunView.fromOutcomes input
      stringResidualMessages [outcomes.string]
  let number ←
    (NumericComputationRunView.fromOutcomes input numberPayloadAt
      numberMessages [outcomes.number]).mapError .numberSource
  pure { string, number }

end CheckedStringToNumberComputationRun

end A12Kernel
