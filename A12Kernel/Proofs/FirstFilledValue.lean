import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Proofs.NumberEntityList

/-! # Resolved Number `FirstFilledValue` laws

These laws characterize the ordered resolved Number scan, its two projections, checked-star partial relevance, and the static multiplicity/direct-uniqueness certificates of checked mixed authoring. They do not prove complete path/tree correspondence, `Having` semantic preservation, the general document/result boundary, target application, or external kernel equivalence.
-/

namespace A12Kernel

/-- The generic lazy scan terminates on a present head without projecting any suffix item. -/
theorem scanFirstFilledItems_present_head
    (cell : α → ValueListCell kind) (head : α) (tail : List α)
    (state : FirstFilledScanState) (atom : ValueListAtom kind)
    (present : cell head = .present atom) :
    scanFirstFilledItems cell (head :: tail) state =
      .inr (.value atom (state.emptyBefore || state.encounteredHaving)) := by
  simp [scanFirstFilledItems, FirstFilledScanState.step, present]

/-- The generic lazy scan likewise terminates on a formally unavailable head without projecting its suffix. -/
theorem scanFirstFilledItems_unknown_head
    (cell : α → ValueListCell kind) (head : α) (tail : List α)
    (state : FirstFilledScanState) (cause : FormalCause)
    (unknown : cell head = .unknown cause) :
    scanFirstFilledItems cell (head :: tail) state =
      .inr (.unavailable cause) := by
  simp [scanFirstFilledItems, FirstFilledScanState.step, unknown]

/-- A present head in the failure-preserving scan returns before any suffix projection and keeps structural failure outside the semantic result. -/
theorem scanFirstFilledItemsResolving_present_head
    (cell : α → Except Error (ValueListCell kind))
    (head : α) (tail : List α) (state : FirstFilledScanState)
    (atom : ValueListAtom kind)
    (present : cell head = .ok (.present atom)) :
    scanFirstFilledItemsResolving cell (head :: tail) state =
      .ok (.inr (.value atom
        (state.emptyBefore || state.encounteredHaving))) := by
  simp [scanFirstFilledItemsResolving, FirstFilledScanState.step,
    present, bind, Except.bind, pure, Except.pure]

/-- A structural failure from the first relevant checked star cell stays outside semantic nonrelevance and unavailability. -/
theorem checkedStarNumberSource_scanResolving_structuralFailure
    (source : CheckedStarNumberSource model)
    (scope : ValidationRelevanceScope)
    (classify : Env → Except Error (ValueListCell .number))
    (environment : Env) (remaining : List Env)
    (state : FirstFilledNumberScanState) (cause : Error)
    (relevant : source.source.cellRelevant scope environment = true)
    (failed : classify environment = .error cause) :
    source.scanPartialValidationFirstFilledStateResolvingWith scope classify
        (environment :: remaining) state = .error cause := by
  simp [CheckedStarNumberSource.scanPartialValidationFirstFilledStateResolvingWith,
    relevant, failed, bind, Except.bind]

/-- The shared filtered first-filled adapter preserves the iterator's successor-before-current order: a poison while locating the successor wins without sampling the pending target classifier. -/
theorem filteredComputationFirstFilled_poisonedSuccessor_precedesCurrent
    (condition : CorrelatedHaving) (filterContext : CorrelationContext)
    (outer first second : Env) (hasUninstantiatedTail : Bool)
    (cell : Env → ValueListCell kind) (state : FirstFilledScanState)
    (cause : FormalCause)
    (firstHolds : condition.evalComputationIn filterContext
      { innerEnv := first, outerEnv := outer } = .holds)
    (secondPoisons : condition.evalComputationIn filterContext
      { innerEnv := second, outerEnv := outer } = .poison cause) :
    scanFilteredComputationFirstFilled condition filterContext outer cell
      [first, second] hasUninstantiatedTail state =
        .inr (.unavailable cause) := by
  simp [scanFilteredComputationFirstFilled,
    CorrelatedHaving.scanComputation,
    CorrelatedHaving.scanComputationCandidates,
    firstHolds, secondPoisons]

private def firstFilledSide
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail : Bool := false)
    (hasHaving : Bool := false) : ResolvedValueListSide .number :=
  { cells, hasUninstantiatedTail, hasHaving }

/-- A present head is selected without observing any suffix or uninstantiated tail. -/
theorem firstFilledNumber_present_head
    (amount : Rat) (tail : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.present amount :: tail)
        hasUninstantiatedTail hasHaving) =
      .value amount hasHaving := by
  cases hasHaving <;> rfl

/-- An unavailable head terminates the scan without observing its suffix. -/
theorem firstFilledNumber_unknown_head
    (cause : FormalCause) (tail : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.unknown cause :: tail)
        hasUninstantiatedTail hasHaving) =
      .unavailable cause := by
  rfl

/-- Any empty prefix makes a later selected value not-given. -/
theorem firstFilledNumber_empty_then_present
    (amount : Rat) (tail : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.empty :: .present amount :: tail)
        hasUninstantiatedTail hasHaving) =
      .value amount true := by
  rfl

/-- Repeating an already-observed empty prefix cannot add another semantic distinction. -/
theorem firstFilledNumber_repeated_empty_prefix
    (cells : List (ValueListCell .number))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide (.empty :: .empty :: cells)
        hasUninstantiatedTail hasHaving) =
    evalFirstFilledNumber
      (firstFilledSide (.empty :: cells)
        hasUninstantiatedTail hasHaving) := by
  rfl

/-- An explicitly all-empty selection supplies the fillable Number zero. -/
theorem firstFilledNumber_explicit_empty_zero
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledNumber
      (firstFilledSide [.empty] hasUninstantiatedTail hasHaving) =
      .value 0 true := by
  rfl

/-- A declared but uninstantiated tail supplies the same fillable Number zero. -/
theorem firstFilledNumber_uninstantiated_zero (hasHaving : Bool) :
    evalFirstFilledNumber (firstFilledSide [] true hasHaving) =
      .value 0 true := by
  rfl

/-- A filter on the admitted operand marks its exhausted empty selection fillable. -/
theorem firstFilledNumber_filtered_empty_zero :
    evalFirstFilledNumber (firstFilledSide [] false true) =
      .value 0 true := by
  rfl

/-- Available selections project to a numeric validation operand with exactly the carried fillability. -/
theorem firstFilledNumber_validation_projection
    (amount : Rat) (notGiven : Bool) :
    (FirstFilledNumberResult.value amount notGiven).asValidationOperand =
      .value amount (if notGiven then .both else .fixed) := by
  cases notGiven <;> rfl

/-- Formal unavailability becomes both an UNKNOWN validation operand and computation poison. -/
theorem firstFilledNumber_unavailable_projections
    (cause : FormalCause) :
    (FirstFilledNumberResult.unavailable cause).asValidationOperand =
        .unknown cause ∧
      (FirstFilledNumberResult.unavailable cause).asComputationResult =
        .poison cause := by
  constructor <;> rfl

/-- Validation distinguishes an earlier empty cell although computation deliberately forgets it. This checked non-law prevents the two projections from being collapsed. -/
theorem firstFilledNumber_empty_prefix_projection_separator
    (amount : Rat) :
    (evalFirstFilledNumber
      (firstFilledSide [.empty, .present amount])).asComputationResult =
        (evalFirstFilledNumber
          (firstFilledSide [.present amount])).asComputationResult ∧
    (evalFirstFilledNumber
      (firstFilledSide [.empty, .present amount])).asValidationOperand ≠
        (evalFirstFilledNumber
          (firstFilledSide [.present amount])).asValidationOperand := by
  rw [firstFilledNumber_empty_then_present amount [] false false,
    firstFilledNumber_present_head amount [] false false]
  constructor
  · rfl
  · intro equal
    have growEqual : true = false := by
      simpa only [FirstFilledNumberResult.asValidationOperand,
        NumericFillability.both, NumericFillability.fixed] using
        congrArg
          (fun operand =>
            match operand with
            | .value _ fillability => fillability.canGrow
            | .unknown _ => false)
          equal
    cases growEqual

/-- A terminal first operand makes every later operand, including its filter marker, unobservable. -/
theorem firstFilledNumberOperands_first_present_hides_rest
    (amount : Rat) (tail : List (ValueListCell .number))
    (later : List (ResolvedValueListSide .number)) :
    evalFirstFilledNumberOperands {
      first := firstFilledSide (.present amount :: tail)
      rest := later } = .value amount false := by
  rfl

/-- A reached filter survives an empty operand boundary and marks a value selected from the next operand fillable. -/
theorem firstFilledNumberOperands_reached_filter_marks_later_value
    (amount : Rat) (tail : List (ValueListCell .number)) :
    evalFirstFilledNumberOperands {
      first := firstFilledSide [] false true
      rest := [firstFilledSide (.present amount :: tail)] } =
      .value amount true := by
  rfl

/-- The runtime wrapper turns a reached selection with no concrete cell into a not-given prefix before a later operand; the separate omitted-tail flag still contributes to the all-exhausted zero identity. -/
theorem firstFilledNumberOperands_no_row_selection_is_empty_prefix
    (amount : Rat) :
    evalFirstFilledNumberOperands {
      first := firstFilledSide [] true
      rest := [firstFilledSide [.present amount]] } = .value amount true ∧
    evalFirstFilledNumberOperands {
      first := firstFilledSide [] true
      rest := [firstFilledSide []] } = .value 0 true := by
  constructor <;> rfl

/-- Successful checked-star evaluation is exactly the established prefix-terminating consumer over the shared checked resolved side. -/
theorem checkedNumericStarSource_evaluateFirstFilled_of_valid
    (checked : CheckedNumericStarSource model) (raw : RawSingleGroupContext)
    (valid : checked.validateContext raw = .ok ()) :
    checked.evaluateFirstFilled raw =
      .ok (evalFirstFilledNumber (checked.resolvedValueSide raw)) := by
  unfold CheckedNumericStarSource.evaluateFirstFilled
  rw [valid]
  rfl

/-- A reached nonrelevant head terminates before either target reader is sampled. -/
theorem checkedStarNumberSource_nonRelevantFirstFilledHeadBeforeRead
    (checked : CheckedStarNumberSource model) (domain : ReopenedStarDomain)
    (environment : Env) (environments : List Env)
    (scope : ValidationRelevanceScope) (left right : Env → FieldId → RawCell)
    (nonRelevant : checked.source.cellRelevant scope environment = false) :
    checked.selectedPartialValidationFirstFilled
        { domain, environments := environment :: environments } scope left = .nonRelevant ∧
      checked.selectedPartialValidationFirstFilled
        { domain, environments := environment :: environments } scope right = .nonRelevant := by
  simp [CheckedStarNumberSource.selectedPartialValidationFirstFilled,
    CheckedStarNumberSource.scanPartialValidationFirstFilled,
    CheckedStarNumberSource.scanPartialValidationFirstFilledState,
    CheckedStarNumberSource.scanPartialValidationFirstFilledStateWith,
    nonRelevant]

/-- A relevant present head selects its value and hides every suffix; arbitrary readers need agree only on that reached classification. -/
theorem checkedStarNumberSource_presentFirstFilledHeadStops
    (checked : CheckedStarNumberSource model) (domain : ReopenedStarDomain)
    (environment : Env) (environments : List Env)
    (scope : ValidationRelevanceScope) (left right : Env → FieldId → RawCell)
    (amount : Rat) (relevant : checked.source.cellRelevant scope environment = true)
    (leftPresent : checked.valueListCell left environment = .present amount)
    (rightPresent : checked.valueListCell right environment = .present amount) :
    checked.selectedPartialValidationFirstFilled
        { domain, environments := environment :: environments } scope left =
          .evaluated (.value amount false) ∧
      checked.selectedPartialValidationFirstFilled
        { domain, environments := environment :: environments } scope right =
          .evaluated (.value amount false) := by
  simp [CheckedStarNumberSource.selectedPartialValidationFirstFilled,
    CheckedStarNumberSource.scanPartialValidationFirstFilled,
    CheckedStarNumberSource.scanPartialValidationFirstFilledState,
    CheckedStarNumberSource.scanPartialValidationFirstFilledStateWith,
    relevant, leftPresent, rightPresent, FirstFilledScanState.enterSelection,
    FirstFilledScanState.enter, FirstFilledScanState.step,
    FirstFilledScanResult.asNumber]

/-- Checked multi-operand authoring always retains either a starred first source or a genuine trailing operand. -/
theorem checkedFirstFilledNumberSource_requiredMultiplicity
    (checked : CheckedFirstFilledNumberSource model) :
    (checked.first.isStar || !checked.rest.isEmpty) = true :=
  checkedNumberEntitySource_requiredMultiplicity checked

/-- Checked multi-operand authoring contains no repeated direct non-wildcard field reference. -/
theorem checkedFirstFilledNumberSource_uniqueDirectOperands
    (checked : CheckedFirstFilledNumberSource model) :
    firstDuplicateDirectFirstFilledNumberField? checked.operands = none :=
  checkedNumberEntitySource_uniqueDirectOperands checked

end A12Kernel
