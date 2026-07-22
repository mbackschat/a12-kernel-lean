import A12Kernel.Elaboration.TokenFirstFilledValue

/-! # Checked token `FirstFilledValue` laws -/

namespace A12Kernel

private def firstFilledTokenSide
    (cells : List (ValueListCell .token))
    (hasUninstantiatedTail : Bool := false)
    (hasHaving : Bool := false) : ResolvedValueListSide .token :=
  { cells, hasUninstantiatedTail, hasHaving }

/-- A present token head is selected without observing its suffix or omitted tail. -/
theorem firstFilledToken_present_head
    (token : String) (tail : List (ValueListCell .token))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledToken
      (firstFilledTokenSide (.present token :: tail)
        hasUninstantiatedTail hasHaving) =
      .value token hasHaving := by
  cases hasHaving <;> rfl

/-- An unavailable token head terminates without observing its suffix. -/
theorem firstFilledToken_unknown_head
    (cause : FormalCause) (tail : List (ValueListCell .token))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledToken
      (firstFilledTokenSide (.unknown cause :: tail)
        hasUninstantiatedTail hasHaving) =
      .unavailable cause := by
  rfl

/-- Any empty token prefix marks a later selected value not-given. -/
theorem firstFilledToken_empty_then_present
    (token : String) (tail : List (ValueListCell .token))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledToken
      (firstFilledTokenSide (.empty :: .present token :: tail)
        hasUninstantiatedTail hasHaving) =
      .value token true := by
  rfl

/-- Exhaustion produces no synthetic String or Enumeration token. -/
theorem firstFilledToken_exhausted_noValue
    (hasUninstantiatedTail hasHaving : Bool) :
    evalFirstFilledToken
      (firstFilledTokenSide [.empty] hasUninstantiatedTail hasHaving) =
      .noValue := by
  rfl

/-- Validation retains empty-prefix polarity although token computation deliberately forgets it. -/
theorem firstFilledToken_empty_prefix_projection_separator (token : String) :
    (evalFirstFilledToken
      (firstFilledTokenSide [.empty, .present token])).asComputationResult =
        (evalFirstFilledToken
          (firstFilledTokenSide [.present token])).asComputationResult ∧
    (evalFirstFilledToken
      (firstFilledTokenSide [.empty, .present token])).asValidationOperand ≠
        (evalFirstFilledToken
          (firstFilledTokenSide [.present token])).asValidationOperand := by
  rw [firstFilledToken_empty_then_present token [] false false,
    firstFilledToken_present_head token [] false false]
  constructor
  · rfl
  · intro equal
    simp [FirstFilledTokenResult.asValidationOperand] at equal

/-- A terminal first token makes every later operand and filter marker unobservable. -/
theorem firstFilledTokenOperands_first_present_hides_rest
    (token : String) (tail : List (ValueListCell .token))
    (later : List (ResolvedValueListSide .token)) :
    evalFirstFilledTokenOperands {
      first := firstFilledTokenSide (.present token :: tail)
      rest := later } = .value token false := by
  rfl

/-- A nonrelevant reached star cell terminates before either target reader is sampled. -/
theorem checkedTokenStar_nonRelevantFirstFilledHeadBeforeRead
    (checked : CheckedTokenStarSource model) (environment : Env)
    (environments : List Env) (state : FirstFilledScanState)
    (scope : ValidationRelevanceScope)
    (left right : Env → FieldId → CheckedCell)
    (nonRelevant : checked.source.cellRelevant scope environment = false) :
    checked.scanPartialFirstFilledState scope left
        (environment :: environments) state = .inr .nonRelevant ∧
      checked.scanPartialFirstFilledState scope right
        (environment :: environments) state = .inr .nonRelevant := by
  simp [CheckedTokenStarSource.scanPartialFirstFilledState, nonRelevant]

/-- Checked token first-filled authoring retains the common multiplicity invariant. -/
theorem checkedFirstFilledTokenSource_requiredMultiplicity
    (checked : CheckedFirstFilledTokenSource model) :
    (checked.first.isStar || !checked.rest.isEmpty) = true :=
  checked.requiredMultiplicity

/-- Checked token first-filled authoring contains no repeated direct field reference. -/
theorem checkedFirstFilledTokenSource_uniqueDirectOperands
    (checked : CheckedFirstFilledTokenSource model) :
    firstDuplicateDirectFirstFilledTokenField? checked.operands = none :=
  checked.uniqueDirectOperands

end A12Kernel
