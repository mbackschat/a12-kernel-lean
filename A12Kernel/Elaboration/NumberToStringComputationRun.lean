import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Semantics.HeterogeneousComputationDependency

/-! # One checked Number-to-String computation run

This capsule executes exactly one checked scalar Number table followed by one checked String table that references the Number target. The Number outcome remains typed and complete; only the String consumer receives the Number target's stored text through the existing reached-read dependency overlay. The result boundary retains each family's established projection instead of erasing them into a common outcome type.

Repeatable activation, additional families, a generic dependency graph, and whole-document application remain separate.
-/

namespace A12Kernel

namespace StringExpr

/-- Whether the expression contains the exact Number-to-text leaf for one field. Ordinary String reads and guard-only references do not satisfy this bounded composition gate. -/
def referencesFieldValueAsString (field : FieldId) :
    StringExpr FieldId → Bool
  | .fieldValueAsString candidate => candidate == field
  | .concat left right =>
      left.referencesFieldValueAsString field ||
        right.referencesFieldValueAsString field
  | .field _ | .literal _ | .range _ _ _ => false

end StringExpr

namespace CheckedStringComputationTable

/-- Whether any String row contains the exact Number-to-text consumer leaf. -/
def consumesNumberAsString
    (table : CheckedStringComputationTable model)
    (field : FieldId) : Bool :=
  table.selectableAlternatives.any fun alternative =>
    alternative.expression.core.referencesFieldValueAsString field

end CheckedStringComputationTable

inductive NumberToStringComputationRunPlanError where
  | numberRequiresRepeatableContext (target : FieldId)
  | numberReadsString (numberTarget stringTarget : FieldId)
  | stringDoesNotConsumeNumberAsString
      (stringTarget numberTarget : FieldId)
  deriving Repr, DecidableEq

/-- One statically ordered heterogeneous run whose consumer is known to reference its scalar Number producer. -/
structure CheckedNumberToStringComputationRun (model : FlatModel) where
  number : CheckedNumericComputationTable model
  string : CheckedStringComputationTable model
  numberScalar : number.supportsScalarEvaluation = true
  numberDoesNotReadString :
    number.referencesField string.targetField = false
  stringConsumesNumberAsString :
    string.consumesNumberAsString number.targetField = true

/-- Certify the exact two-family dependency edge without constructing a general schedule. -/
def certifyNumberToStringComputationRun
    (number : CheckedNumericComputationTable model)
    (string : CheckedStringComputationTable model) :
    Except NumberToStringComputationRunPlanError
      (CheckedNumberToStringComputationRun model) :=
  if hScalar : number.supportsScalarEvaluation = true then
    if hReverse : number.referencesField string.targetField = false then
      if hForward :
          string.consumesNumberAsString number.targetField = true then
        .ok {
          number
          string
          numberScalar := hScalar
          numberDoesNotReadString := hReverse
          stringConsumesNumberAsString := hForward
        }
      else
        .error (.stringDoesNotConsumeNumberAsString
          string.targetField number.targetField)
    else
      .error (.numberReadsString number.targetField string.targetField)
  else
    .error (.numberRequiresRepeatableContext number.targetField)

/-- Exact rich outcomes from the two family owners. Field IDs remain attached so later result projection cannot lose family or target identity. -/
structure NumberToStringComputationOutcomes where
  number : FieldId × NumericTargetOutcome
  string : FieldId × StringTargetOutcome
  deriving Repr, DecidableEq

inductive NumberToStringComputationRunFault where
  | number (cause : NumericComputationRunFault)
  | string (cause : StringComputationRunFault)
  deriving Repr, DecidableEq

namespace CheckedNumberToStringComputationRun

/-- Overlay exactly the completed Number target on the String document context. -/
def stringContext (run : CheckedNumberToStringComputationRun model)
    (input : CheckedDocument model)
    (outcome : NumericTargetOutcome) :
    StringComputationContext :=
  input.stringComputationContext.withDependencyCell
    run.number.targetField
    (StringDependencyCell.ofNumericOutcome outcome)

/-- Execute the Number producer against the immutable document, overlay only its completed dependency observation, and evaluate the reached String consumer. -/
def execute (run : CheckedNumberToStringComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except NumberToStringComputationRunFault
      NumberToStringComputationOutcomes :=
  match run.number.evaluateCompletion
      (input.scalarComputationContext world) with
  | .error cause => .error (.number cause)
  | .ok number =>
      match run.string.evaluateCompletion patterns
          (run.stringContext input number.outcome) with
      | .error cause => .error (.string cause)
      | .ok string => .ok {
          number := (number.targetField, number.outcome)
          string := (string.targetField, string.outcome)
        }

end CheckedNumberToStringComputationRun

/-- Family-preserving public result for the bounded heterogeneous run. -/
structure NumberToStringComputationRunView
    (NumberPayload StringResidual : Type) where
  number :
    NumericComputationRunView (ComputationFormalMessage NumberPayload)
  string : StringComputationRunView StringResidual
  deriving Repr, DecidableEq

inductive NumberToStringComputationRunResultFault where
  | execution (cause : NumberToStringComputationRunFault)
  | numberSource (cause : NumericSourceTargetError)
  deriving Repr, DecidableEq

namespace CheckedNumberToStringComputationRun

/-- Project each rich outcome through its existing family owner while retaining the two result channels separately. -/
def executeResult (run : CheckedNumberToStringComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual) :
    Except NumberToStringComputationRunResultFault
      (NumberToStringComputationRunView NumberPayload StringResidual) := do
  let outcomes ← (run.execute world patterns input).mapError .execution
  let number ←
    (NumericComputationRunView.fromOutcomes input numberPayloadAt
      numberMessages [outcomes.number]).mapError .numberSource
  let string :=
    StringComputationRunView.fromOutcomes input
      stringResidualMessages [outcomes.string]
  pure { number, string }

end CheckedNumberToStringComputationRun

end A12Kernel
