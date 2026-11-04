import A12Kernel.Elaboration.SumOfTerms.Core
import A12Kernel.Elaboration.CheckedStarDocument

/-! # `SumOfTerms` evaluation

The term is evaluated once per kept in-capacity row of the entity, with that row as the candidate
environment and the rule's own row as the captured one, through the same atom readers and the same
generic arithmetic evaluators a filter comparison uses
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)). A row the filter drops,
or whose filter verdict is unknown, adds nothing; over no row the sum is `0`.

**Validation** keeps each row's directional fillability, because the message type needs it. An empty
read counts as zero with its fillability, so its row still adds its other reads; a division by zero
leaves the row no term value and adds nothing. The sum is fixed only when every declared row of the
entity is instantiated, passes the filter and has a term value, and each row's own fillability adds
into it. A row without a term value, an uninstantiated or filtered-out row, leaves it fillable in both
directions. A formally invalid cell the term reads makes the sum unavailable.

**Computation** projects the same reads to the computation result: a row without a value adds nothing,
and a formally invalid cell the term reads, or a filter verdict that poisons, is poison for the whole
sum, which the scan reports at the first row that reaches it.
-/

namespace A12Kernel

/-- One row's validation-phase term outcome: a value with its fillability, no value, or formal
unavailability. -/
abbrev SumOfTermsRowOutcome := Except NumericValidationUnavailable NumericArithmeticOutcome

/-- The running validation sum with the directions in which it can still change. -/
structure SumOfTermsFold where
  total : Rat := 0
  fillability : NumericFillability := .fixed

namespace SumOfTermsFold

/-- Add one row. The first unavailable row stops the sum, a row without a term value adds nothing and
leaves it fillable both ways, and a value adds through the precision-50 arithmetic every sum shares. -/
def step (fold : SumOfTermsFold) : SumOfTermsRowOutcome → Except NumericValidationUnavailable SumOfTermsFold
  | .error cause => .error cause
  | .ok .notEvaluated => .ok { fold with fillability := fold.fillability.add .both }
  | .ok (.value amount fillability) =>
      .ok { total := NumericArithmeticOp.add.eval fold.total amount
            fillability := fold.fillability.add fillability }

/-- The sum as a validation operand. -/
def outcome (fold : SumOfTermsFold) : NumericArithmeticOutcome := .value fold.total fold.fillability

end SumOfTermsFold

/-- The term at one row, in the validation phase, atom by atom through the shared filter readers. -/
def sumOfTermsRowValidation {Error : Type} (term : AuthoredNumericExpr HavingNumericAtom)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error SumOfTermsRowOutcome := do
  let atoms ← term.mapM (HavingNumericAtom.readArithmetic .validation context frame)
  pure (atoms.lowerForEvaluation.evalNumericOperationTree id)

namespace CheckedSumOfTerms

/-- The in-capacity rows the term is evaluated at. An unfiltered entity keeps every row of its
topology. A filtered one keeps the candidates the filter selects that lie in capacity: a row beyond the
declared repeatability is never kept, even by a filter that would keep it. -/
private def validationRows (checked : CheckedSumOfTerms model) (document : CheckedDocument model)
    (outer : Env) (topology : ResolvedStarTopology) (world : Option World) :
    Except CheckedAddressingError (List Env) := do
  match checked.filter with
  | none => pure topology.environments
  | some filter => do
      let traversal ← (model.filterTraversal checked.source.path
        (document.filterRows.getD document.source.instantiatedRows) outer .requireSmall).mapError .addressing
      let selected ← filter.condition.selectEnvironmentsResolving
        (document.resolvingCorrelationContextWithRead document.readDeclared world) outer
        traversal.candidates traversal.occupancy
      pure (selected.filter topology.environments.contains)

/-- The sum in full validation. Structural addressing failure stays an outer error and is never
confused with unavailability. -/
def evaluateValidation (checked : CheckedSumOfTerms model) (document : CheckedDocument model)
    (outer : Env) (world : Option World := none) :
    Except CheckedAddressingError SumOfTermsRowOutcome := do
  let topology ← (checked.source.path.resolveInCapacity document.source.toDocument outer).mapError
    .addressing
  let rows ← checked.validationRows document outer topology world
  let context := document.resolvingCorrelationContextWithRead document.readDeclared world
  let outcomes ← rows.mapM fun row =>
    sumOfTermsRowValidation checked.term context { innerEnv := row, outerEnv := outer }
  let start : SumOfTermsFold :=
    { fillability := if topology.domain.hasOpenTail || !topology.environments.all rows.contains
        then .both else .fixed }
  pure ((outcomes.foldlM SumOfTermsFold.step start).map (·.outcome))

/-- The sum in computation. `filterContext` and `termContext` are the caller's readers of the
filter's cells and of the term's, the two channels a filtered computation operand reads through, and
`addressing` lifts a topology failure into its fault type. -/
def evaluateComputation {Error : Type} (checked : CheckedSumOfTerms model) (document : Document)
    (outer : Env) (filterContext termContext : ResolvingCorrelationContext Error)
    (addressing : StarAddressingError → Error) : Except Error NumericComputationResult := do
  let topology ← (checked.source.path.resolveInCapacity document outer).mapError addressing
  let lowered := checked.term.lowerForEvaluation
  -- One kept row: add a value, add nothing for a division by zero, stop on poison. A row beyond the
  -- capacity is never consumed, though the filter reads it.
  let step (total : Rat) (row : Env) : Except Error (Rat ⊕ NumericComputationResult) := do
    if !topology.environments.contains row then return .inl total
    match ← lowered.evalComputation
        (HavingNumericAtom.readComputationResolving termContext { innerEnv := row, outerEnv := outer }) with
    | .value amount => pure (.inl (NumericArithmeticOp.add.eval total amount))
    | .domainFailure => pure (.inl total)
    | .poison cause => pure (.inr (.poison cause))
  match checked.filter with
  | none =>
      let mut total : Rat := 0
      for row in topology.environments do
        match ← step total row with
        | .inl next => total := next
        | .inr result => return result
      pure (.value total)
  | some filter =>
      let traversal ← (model.filterTraversal checked.source.path
        (document.filterRows.getD document.instantiatedRows) outer .requireSmall).mapError addressing
      match ← filter.condition.scanComputationResolving filterContext outer step traversal.candidates 0
          traversal.occupancy with
      | .exhausted total => pure (.value total)
      | .terminated result => pure result
      | .poison cause => pure (.poison cause)

end CheckedSumOfTerms

end A12Kernel
