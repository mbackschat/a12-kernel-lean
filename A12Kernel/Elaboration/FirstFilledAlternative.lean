import A12Kernel.Elaboration.DocumentComputationStep
import A12Kernel.Elaboration.StringFirstFilledComputation
import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation

/-! # First-filled operations at one selected target instance

The alternative selector must decide before an operation reads any source (spec/09 §1).
Retain existing source/target certificates and per-instance evaluators so the same operation can
serve a standalone row step and a selected alternative without traversing unselected target rows.
-/

namespace A12Kernel

inductive CheckedFirstFilledAlternative (model : FlatModel) where
  | string (operation : CheckedStringFirstFilledComputation model)
  | fixedEnumeration (operation : CheckedEnumerationFirstFilledComputationOperation model)
      (declaration : FlatFieldDecl) (sameField : declaration.id = operation.target.field)
      (fixed : declaration.repeatableScope = [])
  | addressedEnumeration (operation : CheckedAddressedEnumerationFirstFilledComputation model)
  | boolean (operation : CheckedBooleanFirstFilledComputation model)
  | time (operation : CheckedTimeFirstFilledComputation model)
  | dateTime (operation : CheckedDateTimeFirstFilledComputation model)
  | fullDate (operation : CheckedFullDateFirstFilledComputation model)
  | dateRange (operation : CheckedDateRangeFirstFilledComputation model)
  | directDateRange (operation : CheckedDateRangeFirstFilledDirectComputation model)

inductive FirstFilledAlternativeFault where
  | string (cause : StringFirstFilledComputationFault)
  | fixedEnumeration (cause : CheckedAddressingError)
  | enumeration (cause : AddressedEnumerationFirstFilledComputationFault)
  | site (cause : FirstFilledSiteFault)
  | dateTime (cause : DateTimeFirstFilledComputationFault)
  | fullDate (cause : FullDateFirstFilledComputationFault)
  | dateRange (cause : DateRangeFirstFilledComputationFault)
  | readBack (cause : DocumentComputationStepFault)
  deriving Repr, DecidableEq

namespace CheckedFirstFilledAlternative

def target : CheckedFirstFilledAlternative model → FlatFieldDecl
  | .string operation => operation.target
  | .fixedEnumeration _ declaration _ _ => declaration
  | .addressedEnumeration operation => operation.target.declaration
  | .boolean operation => operation.target
  | .time operation => operation.target
  | .dateTime operation => operation.target
  | .fullDate operation => operation.target
  | .dateRange operation => operation.target
  | .directDateRange operation => operation.targetDeclaration

def family : CheckedFirstFilledAlternative model → DocumentTargetFamily
  | .string _ => .string
  | .fixedEnumeration .. | .addressedEnumeration _ => .enumeration
  | .boolean _ => .boolean
  | .time _ => .time
  | .dateTime _ => .dateTime
  | .fullDate _ => .fullDate
  | .dateRange _ | .directDateRange _ => .dateRange

def referencesWith : CheckedFirstFilledAlternative model → FieldId → (CorrelatedHaving → Bool) → Bool
  | .string operation => operation.referencesWith
  | .fixedEnumeration operation _ _ _ => operation.referencesWith
  | .addressedEnumeration operation => operation.source.referencesWith
  | .boolean operation => operation.referencesWith
  | .time operation => operation.referencesWith
  | .dateTime operation => operation.referencesWith
  | .fullDate operation => operation.referencesWith
  | .dateRange operation => operation.referencesWith
  | .directDateRange operation => fun field _ => operation.sources.any (·.direct.source.id == field)

private def targetAddress (target : FlatFieldDecl) (environment : Env)
    (fault : EnvBindingError → FirstFilledAlternativeFault) : Except FirstFilledAlternativeFault CellAddr := do
  let path ← (environment.pathForScope target.repeatableScope).mapError fault
  pure { field := target.id, path }

private def isFilterValueFailure : FirstFilledAlternativeFault → Bool
  | .string (.source error) | .fixedEnumeration error | .enumeration (.source error) | .site (.source error)
  | .dateTime (.site (.source error)) | .fullDate (.site (.source error))
  | .dateRange (.site (.source error)) => error.isFilterValueFailure
  | _ => false

/-- A selected operation uses the current overlay and preserves target-local filter failure (spec/09). -/
def evaluateAt (operation : CheckedFirstFilledAlternative model) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (document : CheckedDocument model)
    (environment : Env) : Except FirstFilledAlternativeFault (DocumentTargetOutcome × CheckedCell) := do
  let result : Except FirstFilledAlternativeFault (DocumentTargetOutcome × CheckedCell) := do
    match operation with
    | .string operation =>
        let some matcher := patterns.targetMatcher? operation.targetField
          | throw (.string (.targetPatternUnavailable operation.targetField))
        let entry ← (operation.evaluateAt (world := some world) matcher document document.read environment).mapError .string
        pure (.string entry.outcome, ← (DocumentComputationReadBack.string entry.outcome).mapError .readBack)
    | .fixedEnumeration operation _ _ _ =>
        let selected ← (operation.source.evaluateCheckedDocumentWithRead (world := some world)
          document document.read environment).mapError .fixedEnumeration
        let outcome := selected.asComputationResult.asExactStringTargetOutcome
        pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)
    | .addressedEnumeration operation =>
        let entry ← (operation.evaluateAtWithRead (world := some world) document document.read environment).mapError .enumeration
        let outcome := entry.result.asExactStringTargetOutcome
        pure (.enumeration outcome, DocumentComputationReadBack.enumeration operation.target.projection outcome)
    | .boolean operation =>
        let address ← targetAddress operation.target environment (.site ∘ .targetEnvironment)
        let entry ← (operation.evaluateAt (world := some world) document document.read address environment).mapError .site
        pure (.boolean entry.result, DocumentComputationReadBack.boolean entry.result)
    | .time operation =>
        let address ← targetAddress operation.target environment (.site ∘ .targetEnvironment)
        let entry ← (operation.evaluateAt (world := some world) document document.read address environment).mapError .site
        pure (.time entry.outcome, ← (DocumentComputationReadBack.time model operation.targetField entry.outcome).mapError .readBack)
    | .dateTime operation =>
        let address ← targetAddress operation.target environment (.dateTime ∘ .site ∘ .targetEnvironment)
        let entry ← (operation.evaluateAt (world := some world) document document.read address environment).mapError .dateTime
        pure (.dateTime entry.outcome, ← (DocumentComputationReadBack.dateTime model operation.targetField entry.outcome).mapError .readBack)
    | .fullDate operation =>
        let address ← targetAddress operation.target environment (.fullDate ∘ .site ∘ .targetEnvironment)
        let entry ← (operation.evaluateAt (world := some world) document document.read address environment).mapError .fullDate
        pure (.fullDate entry.outcome, ← (DocumentComputationReadBack.fullDate model operation.targetField entry.outcome).mapError .readBack)
    | .dateRange operation =>
        let address ← targetAddress operation.target environment (.dateRange ∘ .site ∘ .targetEnvironment)
        let entry ← (operation.evaluateAt (world := some world) document document.read address environment).mapError .dateRange
        let some policy := operation.target.toDateRangeDeclarationPolicy? | throw (.readBack .targetNotReadable)
        pure (.dateRange entry.outcome, ← (DocumentComputationReadBack.dateRange model policy entry.outcome).mapError .readBack)
    | .directDateRange operation =>
        let outcome ← (operation.execute document).mapError .dateRange
        pure (.dateRange outcome, ← (DocumentComputationReadBack.dateRange model operation.target.policy outcome).mapError .readBack)
  match result with
  | .error error =>
      if isFilterValueFailure error then
        pure (.valueError operation.family, DocumentComputationReadBack.poison)
      else throw error
  | result => result

end CheckedFirstFilledAlternative
end A12Kernel
