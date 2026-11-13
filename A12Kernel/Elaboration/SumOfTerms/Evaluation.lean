import A12Kernel.Elaboration.SumOfTerms.Core
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.PartialGroupCount

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

**Computation** projects the same reads to the computation result: a row whose division is by zero adds
nothing, as it does in validation, which no computation row measures (spec/09's general rule would
make it poison),
and a formally invalid cell the term reads, or a filter verdict that poisons, is poison for the whole
sum, which the scan reports at the first row that reaches it.

**Partial validation** decides an unfiltered entity only when every row of its capacity is relevant as a
whole and the instance at row index 1 holds no formally invalid field; otherwise the operand is
undecided, and a filtered entity is skipped with its rule. It reads the term through the call's
availability-aware cell view and folds the rows as full validation does.
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

/-- The sum over `rows`, each read through `context`. The sum is fixed only when every declared row of
the topology is among the kept rows and the declared tail is closed. -/
private def foldRows (checked : CheckedSumOfTerms model)
    (context : ResolvingCorrelationContext CheckedAddressingError) (outer : Env)
    (topology : ResolvedStarTopology) (rows : List Env) :
    Except CheckedAddressingError SumOfTermsRowOutcome := do
  let outcomes ← rows.mapM fun row =>
    sumOfTermsRowValidation checked.term context { innerEnv := row, outerEnv := outer }
  let start : SumOfTermsFold :=
    { fillability := if topology.domain.hasOpenTail || !topology.environments.all rows.contains
        then .both else .fixed }
  pure ((outcomes.foldlM SumOfTermsFold.step start).map (·.outcome))

/-- The sum in full validation. Structural addressing failure stays an outer error and is never
confused with unavailability. -/
def evaluateValidation (checked : CheckedSumOfTerms model) (document : CheckedDocument model)
    (outer : Env) (world : Option World := none) :
    Except CheckedAddressingError SumOfTermsRowOutcome := do
  let topology ← (checked.source.path.resolveInCapacity document.source.toDocument outer).mapError
    .addressing
  let rows ← checked.validationRows document outer topology world
  checked.foldRows (document.resolvingCorrelationContextWithRead document.readDeclared world) outer
    topology rows

/-- The environment of the entity's first declared instance: the bound levels, with every level the
entity reopens at row index 1, whether or not the document holds that row. -/
private def firstInstance (checked : CheckedSumOfTerms model) (outer : Env) :
    Except CheckedAddressingError Env := do
  let bound ← (checked.source.path.boundEnvironment outer).mapError .addressing
  pure (bound ++ (checked.source.path.axes.drop checked.source.path.firstStar).map fun axis => (axis.level, 1))

/-- The sum in partial validation, or `none` when the call leaves it undecided. It is decided only when
every row of the entity's capacity is relevant as a whole, the wholly relevant group instances of
`NumberOfFilledGroups` in partial validation ([`coversGroupCountExtent`](#A12Kernel.ValidationRelevanceScope.coversGroupCountExtent)),
so relevance of only the fields the term reads is not enough. The relevant document must also hold no
formally invalid field in the instance at row index 1, while a defect in row 2 or 3 blocks nothing: the
gate asks of that index, not of the first row held. Validation pads a document that places no row 1 to
an empty instantiated row 1, so this checked document never lacks one
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms), a12-dmkits
`SumOfTermsRuntimeLawsTest` and `SumOfTermsShapesRuntimeLawsTest` at `1124b523f`, kernel 31.1.1).

The gate reads every field of the instance, term or not: a malformed field the term never reads blocks
it too (the same peer rows). Unmeasured: a read outside the entity must be relevant at the rule's own
row, a nested entity asks the instance at row 1 of every reopened level, and a read of a cell the call
leaves unavailable surfaces as `partialUnavailable`. The caller has applied the rule-wide filter skip and
[`supportsPartial`](#A12Kernel.CheckedSumOfTerms.supportsPartial). -/
def evaluatePartial (checked : CheckedSumOfTerms model) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) (isRelevant : FlatRelevance)
    (read : Env → FieldId → Except CheckedAddressingError CheckedCell)
    (resolveGroup : PartialGroupResolver) (world : Option World := none) :
    Except CheckedAddressingError (Option SumOfTermsRowOutcome) := do
  let entityFields := model.groupSubtreeFields checked.source.group.path
  let outside := (checked.term.atoms.flatMap (·.fieldOrigins)).map (·.2) |>.filter fun field =>
    !entityFields.any (·.id == field)
  if !scope.coversGroupCountExtent model checked.source.group.path checked.source.path.bindingScope
        checked.source.path.reopenedScope outer || !outside.all isRelevant then
    return none
  let first ← checked.firstInstance outer
  if (← resolveGroup checked.source.group.path first).derive.erroneous then return none
  let topology ← (checked.source.path.resolveInCapacity document.source.toDocument outer).mapError
    .addressing
  let context := { document.resolvingCorrelationContextWithRead document.readDeclared world with read }
  some <$> checked.foldRows context outer topology topology.environments

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
    -- A term's power raise reads as the domain failure the sum skips; the Kernel's answer on a term
    -- is unmeasured (SG5), while a division by zero there is measured as skipped.
    match ← lowered.evalComputation none
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
