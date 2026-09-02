import A12Kernel.Semantics.NumericLiteral

/-! # Mandatory-information derivation

This module models the measured flat, nonrepeatable contributing fragment of the model-level mandatory-information service plus the exact unfiltered singleton-field presence matrix over one direct unindexed repeatable child of a nonrepeatable root and checked whole-rule no-contribution identities. The input retains normalized authored rule shape, the exact retained two-level negative-field Boolean matrix, the two measured declaration-derived field-required modes, the generated requirement for one optional repeatable String index field, and the generated validation for one direct nonrepeatable scale-0 Number copy, including ignored WARNING and INFO severity; the output keeps global fields, root-relative fields, and mandatory roots independent. The bounded count slice retains authored literals separately from their narrowed host values, keeps filled-count and distinct-count rules separate where their guard behavior differs, accepts the exact field-guard dependency roles measured for one filled-count operand and its target plus one target-to-count-operand chain across six measured count/contiguous-seed category orders, and retains the measured isolated distinct-count comparison matrix as no-contribution. The filled-field guard slice retains existential versus universal rule identity, and finite field-guard cycles participate in the same monotone closure as acyclic chains. The semantic-indexed, parallel-iterated, and cross-root captures establish referenced-field exclusion; the checked identities additionally contribute no roots, with only the cross-root capture separating its non-control root. Wider repetition, concrete indices, wider semantic-index shapes, filter internals, other generated index and computation-validation shapes, contributing cross-root rules, wider root topology, wider count sites, and Boolean formulas beyond the exact retained matrix remain outside this carrier. -/

namespace A12Kernel

/-- One numeric count threshold after exact decimal decoding and the measured host conversion. The private constructor prevents an authored literal from being paired with an unrelated narrowed value. -/
structure CheckedMandatoryCountThreshold where
  private mk ::
  authored : DecodedNumericLiteral
  narrowed : Int
  deriving Repr, DecidableEq

/-- Check one authored finite-decimal threshold without replacing its identity by the narrowed host integer. -/
def checkMandatoryCountThreshold (authored : DecodedNumericLiteral) :
    Option CheckedMandatoryCountThreshold := do
  let narrowed ← authored.javaRoundedInt32?
  pure { authored, narrowed }

/-- Measured count-guard spellings. Reversed forms stay distinct even when they share a numeric relation with a count-on-left comparison. -/
inductive MandatoryCountGuardComparison where
  | countGreaterEqual
  | countGreater
  | literalLessEqualCount
  | literalLessThanCount
  deriving Repr, DecidableEq

namespace MandatoryCountGuardComparison

private def holds (comparison : MandatoryCountGuardComparison)
    (count threshold : Int) : Bool :=
  match comparison with
  | .countGreaterEqual | .literalLessEqualCount => decide (threshold ≤ count)
  | .countGreater | .literalLessThanCount => decide (threshold < count)

end MandatoryCountGuardComparison

/-- Flat filled-field guard identities whose entailment may expose a mandatory target. -/
inductive MandatoryFieldListGuard where
  | atLeastOneFilled
  | allFilled
  deriving Repr, DecidableEq

/-- The two measured top-level compositions between one ordinary negative field and one unfiltered repeatable presence quantifier. -/
inductive MandatoryPresenceConnective where
  | conjunction
  | disjunction
  deriving Repr, DecidableEq

/-- The measured singleton starred-field presence operators in the repeatable mandatory-information matrix. -/
inductive RepeatableFieldPresenceQuantifier where
  | noFieldFilled
  | notAllFieldsFilled
  | atLeastOneFieldFilled
  deriving Repr, DecidableEq

/-- The measured topology stays distinct from every wider repeatable-presence scope. -/
inductive MandatoryRepeatablePresenceScope where
  | directUnindexedChildOfNonrepeatableRoot
  | outsideMeasuredScope
  deriving Repr, DecidableEq

namespace MandatoryFieldListGuard

private def holds [DecidableEq Field] (guard : MandatoryFieldListGuard)
    (mandatory premises : List Field) : Bool :=
  match guard with
  | .atLeastOneFilled => premises.any (· ∈ mandatory)
  | .allFilled => premises.all (· ∈ mandatory)

end MandatoryFieldListGuard

/-- Field declaration modes whose mandatory-information result is measured in the flat carrier. -/
inductive DeclaredFieldRequirement where
  | always
  | ifParentPresent
  deriving Repr, DecidableEq

/-- Measured authored or model-derived rule identities that remain visible to Analyze and Explain but have no contribution in this fragment. -/
inductive IgnoredMandatoryRule (Field Root : Type) where
  | fieldFilled (field : Field)
  | fieldsNotCollectivelyFilled (fields : List Field)
  | atLeastOneFieldFilled (fields : List Field)
  | allFieldsFilled (fields : List Field)
  | groupFilled (root : Root)
  | warningFieldNotFilled (field : Field)
  | infoFieldNotFilled (field : Field)
  | filtered (fields : List Field)
  | semanticIndexed (fields : List Field)
  | parallelIterated (fields : List Field)
  | crossRoot (fields : List Field)
  | generatedOptionalRepeatableStringIndexField (field : Field)
  | generatedDirectNonrepeatableScale0NumberCopyValidation (source target : Field)
  deriving Repr, DecidableEq

/-- Measured pure negative-field Boolean shapes. The outer and inner connectives remain explicit because the collector does not simplify logically related formulas to one field contribution. -/
inductive MandatoryNegativeFieldFormula (Field : Type) where
  | flatDisjunction (fields : List Field)
  | conjunctionOfDisjunctions (clauses : List (List Field))
  | disjunctionOfConjunctions (clauses : List (List Field))
  deriving Repr, DecidableEq

namespace MandatoryNegativeFieldFormula

def referencedFields : MandatoryNegativeFieldFormula Field → List Field
  | .flatDisjunction fields => fields
  | .conjunctionOfDisjunctions clauses
  | .disjunctionOfConjunctions clauses => clauses.flatten

private def threeDistinct [DecidableEq Field] (first second third : Field) : Bool :=
  [first, second, third].eraseDups.length == 3

/-- Recognize a two-clause, width-two matrix with one field shared in any measured operand position. -/
private def hasOneSharedField [DecidableEq Field]
    (first second third fourth : Field) : Bool :=
  first != second && third != fourth &&
    [first, second, third, fourth].eraseDups.length == 3

/-- Admit only the retained Boolean-formula matrices rather than extrapolating to arbitrary nesting or arity. -/
def hasMeasuredShape [DecidableEq Field] : MandatoryNegativeFieldFormula Field → Bool
  | .flatDisjunction [first, second, third] =>
      threeDistinct first second third
  | .conjunctionOfDisjunctions [[first, second], [third, fourth]] =>
      hasOneSharedField first second third fourth
  | .conjunctionOfDisjunctions [[left, right], [other]] =>
      threeDistinct left right other
  | .disjunctionOfConjunctions [[first, second], [third, fourth]] =>
      hasOneSharedField first second third fourth
  | _ => false

end MandatoryNegativeFieldFormula

/-- Normalized, measured inputs for flat mandatory-information derivation. Constructors preserve declaration and authored-rule distinctions even where two shapes have the same derived effect. -/
inductive MandatoryRule (Field Root : Type) where
  | declaredFieldRequirement (requirement : DeclaredFieldRequirement) (field : Field)
  | fieldNotFilled (field : Field)
  | disjoinedFieldNotFilled (fields : List Field)
  | conjoinedFieldNotFilled (fields : List Field)
  | notAllFieldsFilled (fields : List Field)
  | noFieldFilled (fields : List Field)
  | notExactlyOneFieldFilled (fields : List Field)
  | groupNotFilled (root : Root)
  | fieldGuardedNotFilled (premise target : Field)
  | rootGuardedNotFilled (premise : Root) (target : Field)
  | fieldListGuardedNotFilled (premises : List Field)
      (guard : MandatoryFieldListGuard) (target : Field)
  | negativeFieldFormula (formula : MandatoryNegativeFieldFormula Field)
  | unfilteredRepeatableFieldPresenceComposition
      (scope : MandatoryRepeatablePresenceScope)
      (connective : MandatoryPresenceConnective)
      (quantifier : RepeatableFieldPresenceQuantifier)
      (field repeatableField : Field)
  | countLessThan (fields : List Field)
      (threshold : Option CheckedMandatoryCountThreshold)
  | countGuardedNotFilled (fields : List Field)
      (comparison : MandatoryCountGuardComparison)
      (threshold : Option CheckedMandatoryCountThreshold) (target : Field)
  | differentValuesLessThan (fields : List Field)
      (threshold : Option CheckedMandatoryCountThreshold)
  | differentValuesGuardedNotFilled (fields : List Field)
      (comparison : MandatoryCountGuardComparison)
      (threshold : Option CheckedMandatoryCountThreshold) (target : Field)
  | ignored (rule : IgnoredMandatoryRule Field Root)
  deriving Repr, DecidableEq

/-- The three public result sets. Lists are duplicate-free and preserve first derivation order; their order carries no semantic meaning. -/
structure MandatoryInformation (Field Root : Type) where
  mandatory : List Field := []
  mandatoryForRootGroup : List Field := []
  mandatoryRootGroups : List Root := []
  deriving Repr, DecidableEq

namespace MandatoryInformationDerivation

private def appendDistinct [DecidableEq α] (current additions : List α) : List α :=
  additions.foldl (fun result item =>
    if item ∈ result then result else result ++ [item]) current

private def intersectPreservingLeft [DecidableEq α]
    (left right : List α) : List α :=
  left.filter (· ∈ right)

private def negativeFormulaRequiredFields [DecidableEq Field] :
    MandatoryNegativeFieldFormula Field → List Field
  | .flatDisjunction fields => fields
  | .conjunctionOfDisjunctions [] => []
  | .conjunctionOfDisjunctions (first :: rest) =>
      rest.foldl intersectPreservingLeft first
  | .disjunctionOfConjunctions clauses =>
      clauses.foldl (fun fields clause =>
        match clause with
        | [field] => appendDistinct fields [field]
        | _ => fields) []

private structure State (Field Root : Type) where
  fields : List Field := []
  roots : List Root := []

private def State.addRoots [DecidableEq Root] (state : State Field Root)
    (roots : List Root) : State Field Root :=
  { state with roots := appendDistinct state.roots roots }

private def State.addFields [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (state : State Field Root)
    (fields : List Field) : State Field Root :=
  {
    fields := appendDistinct state.fields fields
    roots := appendDistinct state.roots (fields.map rootOf)
  }

private def State.countFields [DecidableEq Field] (state : State Field Root)
    (fields : List Field) : Int :=
  fields.foldl (fun count field =>
    if field ∈ state.fields then count + 1 else count) 0

private def countThresholdValue : Option CheckedMandatoryCountThreshold → Int
  | none => -1
  | some threshold => threshold.narrowed

private def hasAuthoredScaleZeroThreshold
    (threshold : Option CheckedMandatoryCountThreshold) (value : Rat) : Bool :=
  match threshold with
  | some checked =>
      checked.authored.value == value && checked.authored.authoredScale == 0
  | none => false

private def hasIsolatedDistinctThreshold
    (comparison : MandatoryCountGuardComparison)
    (threshold : Option CheckedMandatoryCountThreshold) : Bool :=
  match comparison with
  | .countGreaterEqual | .literalLessEqualCount =>
      hasAuthoredScaleZeroThreshold threshold 0 ||
        hasAuthoredScaleZeroThreshold threshold 1
  | .countGreater | .literalLessThanCount =>
      hasAuthoredScaleZeroThreshold threshold (-2) ||
        hasAuthoredScaleZeroThreshold threshold 0

private def MandatoryRule.referencedRoots (rootOf : Field → Root) :
    MandatoryRule Field Root → List Root
  | .declaredFieldRequirement _ field
  | .fieldNotFilled field => [rootOf field]
  | .disjoinedFieldNotFilled fields
  | .conjoinedFieldNotFilled fields
  | .notAllFieldsFilled fields
  | .noFieldFilled fields
  | .notExactlyOneFieldFilled fields => fields.map rootOf
  | .groupNotFilled root => [root]
  | .fieldGuardedNotFilled premise target => [rootOf premise, rootOf target]
  | .rootGuardedNotFilled premise target => [premise, rootOf target]
  | .fieldListGuardedNotFilled premises _ target =>
      premises.map rootOf ++ [rootOf target]
  | .negativeFieldFormula formula => formula.referencedFields.map rootOf
  | .unfilteredRepeatableFieldPresenceComposition _ _ _ field repeatableField =>
      [rootOf field, rootOf repeatableField]
  | .countLessThan fields _
  | .differentValuesLessThan fields _ => fields.map rootOf
  | .countGuardedNotFilled fields _ _ target =>
      fields.map rootOf ++ [rootOf target]
  | .differentValuesGuardedNotFilled fields _ _ target =>
      fields.map rootOf ++ [rootOf target]
  | .ignored (.fieldFilled field)
  | .ignored (.warningFieldNotFilled field)
  | .ignored (.infoFieldNotFilled field)
  | .ignored (.generatedOptionalRepeatableStringIndexField field) => [rootOf field]
  | .ignored (.generatedDirectNonrepeatableScale0NumberCopyValidation source target) =>
      [rootOf source, rootOf target]
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields)
  | .ignored (.semanticIndexed fields)
  | .ignored (.parallelIterated fields) => fields.map rootOf
  | .ignored (.crossRoot _) => []
  | .ignored (.groupFilled root) => [root]

private def MandatoryRule.apply [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (state : State Field Root) :
    MandatoryRule Field Root → State Field Root
  | .declaredFieldRequirement .always field => state.addFields rootOf [field]
  | .declaredFieldRequirement .ifParentPresent field =>
      if rootOf field ∈ state.roots then
        state.addFields rootOf [field]
      else
        state
  | .fieldNotFilled field => state.addFields rootOf [field]
  | .disjoinedFieldNotFilled fields
  | .notAllFieldsFilled fields => state.addFields rootOf fields
  | .conjoinedFieldNotFilled fields
  | .noFieldFilled fields
  | .notExactlyOneFieldFilled fields => state.addRoots (fields.map rootOf)
  | .groupNotFilled root => state.addRoots [root]
  | .fieldGuardedNotFilled premise target =>
      if premise ∈ state.fields then
        state.addFields rootOf [target]
      else
        state
  | .rootGuardedNotFilled premise target =>
      if premise ∈ state.roots then
        state.addFields rootOf [target]
      else
        state
  | .fieldListGuardedNotFilled premises guard target =>
      if guard.holds state.fields premises then
        state.addFields rootOf [target]
      else
        state
  | .negativeFieldFormula formula =>
      let rooted := state.addRoots (formula.referencedFields.map rootOf)
      rooted.addFields rootOf (negativeFormulaRequiredFields formula)
  | .unfilteredRepeatableFieldPresenceComposition _ .disjunction
      .notAllFieldsFilled field repeatableField =>
      state.addFields rootOf [field, repeatableField]
  | .unfilteredRepeatableFieldPresenceComposition _ .disjunction _ field _ =>
      state.addFields rootOf [field]
  | .unfilteredRepeatableFieldPresenceComposition _ .conjunction
      .atLeastOneFieldFilled _ _ => state
  | .unfilteredRepeatableFieldPresenceComposition _ .conjunction _ field repeatableField =>
      state.addRoots [rootOf field, rootOf repeatableField]
  | .countLessThan fields threshold
  | .differentValuesLessThan fields threshold =>
      if 0 < countThresholdValue threshold then
        state.addRoots (fields.map rootOf)
      else
        state
  | .countGuardedNotFilled fields comparison threshold target =>
      let thresholdValue := countThresholdValue threshold
      if thresholdValue != -1 &&
          comparison.holds (state.countFields fields) thresholdValue then
        state.addFields rootOf [target]
      else
        state
  | .differentValuesGuardedNotFilled _ _ _ _ => state
  | .ignored _ => state

private def step [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (rules : List (MandatoryRule Field Root))
    (state : State Field Root) : State Field Root :=
  rules.foldl (fun current rule => MandatoryRule.apply rootOf current rule) state

private def close [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (rules : List (MandatoryRule Field Root)) :
    Nat → State Field Root → State Field Root
  | 0, state => state
  | fuel + 1, state =>
      close rootOf rules fuel (step rootOf rules state)

private def referencedRoots [DecidableEq Root] (rootOf : Field → Root)
    (rules : List (MandatoryRule Field Root)) : List Root :=
  rules.foldl (fun roots rule =>
    appendDistinct roots (MandatoryRule.referencedRoots rootOf rule)) []

private def MandatoryRule.hasNonemptyLists : MandatoryRule Field Root → Bool
  | .disjoinedFieldNotFilled fields
  | .conjoinedFieldNotFilled fields
  | .notAllFieldsFilled fields
  | .noFieldFilled fields
  | .notExactlyOneFieldFilled fields => !fields.isEmpty
  | .fieldListGuardedNotFilled premises _ _ => !premises.isEmpty
  | .negativeFieldFormula formula => !formula.referencedFields.isEmpty
  | .countLessThan fields _
  | .differentValuesLessThan fields _
  | .countGuardedNotFilled fields _ _ _
  | .differentValuesGuardedNotFilled fields _ _ _ => !fields.isEmpty
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields)
  | .ignored (.semanticIndexed fields)
  | .ignored (.parallelIterated fields)
  | .ignored (.crossRoot fields) => !fields.isEmpty
  | _ => true

private def MandatoryRule.hasSupportedFieldListGuardShape [DecidableEq Field] :
    MandatoryRule Field Root → Bool
  | .fieldListGuardedNotFilled premises _ _ =>
      premises.eraseDups == premises
  | _ => true

private def MandatoryRule.hasSupportedRepeatablePresenceScope :
    MandatoryRule Field Root → Bool
  | .unfilteredRepeatableFieldPresenceComposition .outsideMeasuredScope _ _ _ _ => false
  | _ => true

private def MandatoryRule.isNegativeFieldFormula :
    MandatoryRule Field Root → Bool
  | .negativeFieldFormula _ => true
  | _ => false

private def hasSupportedNegativeFieldFormulaShape [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : Bool :=
  if rules.any MandatoryRule.isNegativeFieldFormula then
    match rules with
    | [.negativeFieldFormula formula] => formula.hasMeasuredShape
    | _ => false
  else
    true

private def directFieldSeeds [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : List Field :=
  rules.foldl (fun seeds rule =>
    match rule with
    | .fieldNotFilled field => appendDistinct seeds [field]
    | _ => seeds) []

private def MandatoryRule.countShapeFields : MandatoryRule Field Root → List Field
  | .declaredFieldRequirement _ field
  | .fieldNotFilled field => [field]
  | .disjoinedFieldNotFilled fields
  | .conjoinedFieldNotFilled fields
  | .notAllFieldsFilled fields
  | .noFieldFilled fields
  | .notExactlyOneFieldFilled fields => fields
  | .groupNotFilled _ => []
  | .fieldGuardedNotFilled premise target => [premise, target]
  | .rootGuardedNotFilled _ target => [target]
  | .fieldListGuardedNotFilled premises _ target => premises ++ [target]
  | .negativeFieldFormula formula => formula.referencedFields
  | .unfilteredRepeatableFieldPresenceComposition _ _ _ field repeatableField =>
      [field, repeatableField]
  | .countLessThan fields _
  | .differentValuesLessThan fields _ => fields
  | .countGuardedNotFilled fields _ _ target => fields ++ [target]
  | .differentValuesGuardedNotFilled fields _ _ target => fields ++ [target]
  | .ignored (.fieldFilled field)
  | .ignored (.warningFieldNotFilled field)
  | .ignored (.infoFieldNotFilled field) => [field]
  | .ignored (.generatedOptionalRepeatableStringIndexField _)
  | .ignored (.generatedDirectNonrepeatableScale0NumberCopyValidation _ _) => []
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields)
  | .ignored (.semanticIndexed fields)
  | .ignored (.parallelIterated fields)
  | .ignored (.crossRoot fields) => fields
  | .ignored (.groupFilled _) => []

private def fieldMentionCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    (MandatoryRule.countShapeFields rule).foldl (fun count mentioned =>
      if mentioned = field then count + 1 else count) count) 0

private def countFamilyOperandCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    match rule with
    | .countLessThan fields _
    | .countGuardedNotFilled fields _ _ _
    | .differentValuesLessThan fields _
    | .differentValuesGuardedNotFilled fields _ _ _ =>
        if field ∈ fields then count + 1 else count
    | _ => count) 0

private def isSupportedDistinctSeedOperand [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (seeds : List Field)
    (field : Field) : Bool :=
  field ∈ seeds &&
    fieldMentionCount rules field == countFamilyOperandCount rules field + 1

private def countGuardOperandCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    match rule with
    | .countGuardedNotFilled fields _ _ _ =>
        if field ∈ fields then count + 1 else count
    | _ => count) 0

private def directSeededFieldGuardTargetCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (seeds : List Field)
    (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    match rule with
    | .fieldGuardedNotFilled premise target =>
        if target = field && premise ∈ seeds then count + 1 else count
    | _ => count) 0

private def countGuardTargetCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    match rule with
    | .countGuardedNotFilled _ _ _ target =>
        if target = field then count + 1 else count
    | _ => count) 0

private def fieldGuardPremiseCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    match rule with
    | .fieldGuardedNotFilled premise _ =>
        if premise = field then count + 1 else count
    | _ => count) 0

private def isMeasuredCountTargetOperand [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Bool :=
  countGuardTargetCount rules field == 1 &&
    countGuardOperandCount rules field == 1 &&
    fieldMentionCount rules field == 2

private def isSupportedCountOperand [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (seeds : List Field)
    (field : Field) : Bool :=
  field ∈ seeds || fieldMentionCount rules field == 1 ||
    (countGuardOperandCount rules field == 1 &&
      directSeededFieldGuardTargetCount rules seeds field == 1 &&
      fieldMentionCount rules field == 2) ||
    isMeasuredCountTargetOperand rules field

private def isSupportedCountTarget [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Bool :=
  let targetCount := countGuardTargetCount rules field
  let premiseCount := fieldGuardPremiseCount rules field
  (targetCount == 1 &&
    fieldMentionCount rules field == targetCount + premiseCount) ||
    isMeasuredCountTargetOperand rules field

private def hasCountTargetOperandRole [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : Bool :=
  rules.any fun
    | .countGuardedNotFilled _ _ _ target =>
        countGuardOperandCount rules target != 0
    | _ => false

private def matchesMeasuredCountTargetOperandChain
    [DecidableEq Field]
    (downstreamFields upstreamFields : List Field)
    (downstreamComparison upstreamComparison : MandatoryCountGuardComparison)
    (downstreamThreshold upstreamThreshold : Option CheckedMandatoryCountThreshold)
    (downstreamTarget upstreamTarget : Field) (allowDownstreamTwo : Bool)
    (seeds : List Field) : Bool :=
  match downstreamFields, upstreamFields with
  | [bridge, downstreamOther], [left, right] =>
      [bridge, downstreamOther, downstreamTarget, left, right].eraseDups.length == 5 &&
        bridge == upstreamTarget &&
        downstreamComparison == .countGreaterEqual &&
        upstreamComparison == .countGreaterEqual &&
        (hasAuthoredScaleZeroThreshold downstreamThreshold 1 ||
          (allowDownstreamTwo &&
            hasAuthoredScaleZeroThreshold downstreamThreshold 2)) &&
        hasAuthoredScaleZeroThreshold upstreamThreshold 2 &&
        (seeds == [left] || seeds == [left, right])
  | _, _ => false

private def matchesMeasuredCountTargetOperandChainInEitherDirection
    [DecidableEq Field]
    (firstFields secondFields : List Field)
    (firstComparison secondComparison : MandatoryCountGuardComparison)
    (firstThreshold secondThreshold : Option CheckedMandatoryCountThreshold)
    (firstTarget secondTarget : Field) (seeds : List Field) : Bool :=
  matchesMeasuredCountTargetOperandChain firstFields secondFields
      firstComparison secondComparison firstThreshold secondThreshold
      firstTarget secondTarget false seeds ||
    matchesMeasuredCountTargetOperandChain secondFields firstFields
      secondComparison firstComparison secondThreshold firstThreshold
      secondTarget firstTarget false seeds

private def matchesMeasuredCanonicalCountTargetOperandChain
    [DecidableEq Field]
    (firstFields secondFields : List Field)
    (firstComparison secondComparison : MandatoryCountGuardComparison)
    (firstThreshold secondThreshold : Option CheckedMandatoryCountThreshold)
    (firstTarget secondTarget : Field) (seeds : List Field) : Bool :=
  matchesMeasuredCountTargetOperandChain firstFields secondFields
      firstComparison secondComparison firstThreshold secondThreshold
      firstTarget secondTarget true seeds ||
    matchesMeasuredCountTargetOperandChain secondFields firstFields
      secondComparison firstComparison secondThreshold firstThreshold
      secondTarget firstTarget false seeds

private def hasSupportedCountTargetOperandShape [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : Bool :=
  if !hasCountTargetOperandRole rules then
    true
  else
    match rules with
    | [.countGuardedNotFilled firstFields firstComparison firstThreshold firstTarget,
        .countGuardedNotFilled secondFields secondComparison secondThreshold secondTarget,
        .fieldNotFilled left] =>
        matchesMeasuredCountTargetOperandChainInEitherDirection firstFields secondFields
          firstComparison secondComparison firstThreshold secondThreshold
          firstTarget secondTarget [left]
    | [.countGuardedNotFilled firstFields firstComparison firstThreshold firstTarget,
        .fieldNotFilled left,
        .countGuardedNotFilled secondFields secondComparison secondThreshold secondTarget] =>
        matchesMeasuredCanonicalCountTargetOperandChain firstFields secondFields
          firstComparison secondComparison firstThreshold secondThreshold
          firstTarget secondTarget [left]
    | [.fieldNotFilled left,
        .countGuardedNotFilled firstFields firstComparison firstThreshold firstTarget,
        .countGuardedNotFilled secondFields secondComparison secondThreshold secondTarget] =>
        matchesMeasuredCountTargetOperandChainInEitherDirection firstFields secondFields
          firstComparison secondComparison firstThreshold secondThreshold
          firstTarget secondTarget [left]
    | [.countGuardedNotFilled firstFields firstComparison firstThreshold firstTarget,
        .countGuardedNotFilled secondFields secondComparison secondThreshold secondTarget,
        .fieldNotFilled left, .fieldNotFilled right] =>
        matchesMeasuredCountTargetOperandChainInEitherDirection firstFields secondFields
          firstComparison secondComparison firstThreshold secondThreshold
          firstTarget secondTarget [left, right]
    | [.countGuardedNotFilled firstFields firstComparison firstThreshold firstTarget,
        .fieldNotFilled left, .fieldNotFilled right,
        .countGuardedNotFilled secondFields secondComparison secondThreshold secondTarget] =>
        matchesMeasuredCanonicalCountTargetOperandChain firstFields secondFields
          firstComparison secondComparison firstThreshold secondThreshold
          firstTarget secondTarget [left, right]
    | [.fieldNotFilled left, .fieldNotFilled right,
        .countGuardedNotFilled firstFields firstComparison firstThreshold firstTarget,
        .countGuardedNotFilled secondFields secondComparison secondThreshold secondTarget] =>
        matchesMeasuredCountTargetOperandChainInEitherDirection firstFields secondFields
          firstComparison secondComparison firstThreshold secondThreshold
          firstTarget secondTarget [left, right]
    | _ => false

/-- Keep each count guard on its measured shape. Filled-count operands are direct singleton seeds, otherwise isolated, the target of one direct-seeded field guard, or the upstream target in the exact two-stage chain across its six measured count/contiguous-seed category orders; only the canonical order also admits downstream threshold `2`. A count target may otherwise be isolated or feed ordinary field guards. Distinct-count guards accept exactly the two-operand direct-seed `>= 2` shape and the measured isolated target-only adjacent pair for each comparison spelling, including authored scale. Explanation-only generated identities participate in topology but not count-shape isolation, and wider dependency or reuse roles stay outside this slice. -/
private def MandatoryRule.hasSupportedCountShape [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (seeds : List Field) :
    MandatoryRule Field Root → Bool
  | .countLessThan fields _
  | .differentValuesLessThan fields _ => fields.eraseDups == fields
  | .countGuardedNotFilled fields _ _ target =>
      fields.eraseDups == fields &&
        fields.all (isSupportedCountOperand rules seeds) &&
        isSupportedCountTarget rules target
  | .differentValuesGuardedNotFilled fields comparison threshold target =>
      let seeded :=
        fields.length == 2 && comparison == .countGreaterEqual &&
          hasAuthoredScaleZeroThreshold threshold 2 &&
          fields.all (isSupportedDistinctSeedOperand rules seeds)
      let isolatedTargetOnly :=
        fields.length == 2 &&
          hasIsolatedDistinctThreshold comparison threshold &&
          fields.all (fun field => fieldMentionCount rules field == 1)
      fields.eraseDups == fields && fieldMentionCount rules target == 1 &&
        (seeded || isolatedTargetOnly)
  | _ => true

private def hasSupportedCountShapes [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : Bool :=
  let seeds := directFieldSeeds rules
  rules.all (MandatoryRule.hasSupportedCountShape rules seeds)

private def MandatoryRule.isDeclaredFieldRequirement :
    MandatoryRule Field Root → Bool
  | .declaredFieldRequirement _ _ => true
  | _ => false

private def MandatoryRule.isDeclaredRequirementClosureRule :
    MandatoryRule Field Root → Bool
  | .declaredFieldRequirement _ _
  | .fieldNotFilled _
  | .groupNotFilled _
  | .ignored (.generatedOptionalRepeatableStringIndexField _)
  | .ignored (.generatedDirectNonrepeatableScale0NumberCopyValidation _ _) => true
  | _ => false

/-- Declaration-derived requirements share root closure only with the measured direct field and root seeds; wider authored interactions remain unmeasured. -/
private def hasSupportedDeclaredFieldRequirementShape
    (rules : List (MandatoryRule Field Root)) : Bool :=
  !rules.any MandatoryRule.isDeclaredFieldRequirement ||
    rules.all MandatoryRule.isDeclaredRequirementClosureRule

private def hasSingleRootTopology [DecidableEq Root] (rootOf : Field → Root)
    (rules : List (MandatoryRule Field Root)) : Bool :=
  match referencedRoots rootOf rules with
  | [] | [_] => true
  | _ => false

end MandatoryInformationDerivation

/-- Derive the three measured mandatory-information sets. One monotone pass per rule is sufficient for every finite dependency chain expressible by this carrier, including reverse-authored chains. Root-relative analysis starts with every referenced root available while global analysis starts without such an assumption. -/
private def deriveMandatoryInformation [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (rules : List (MandatoryRule Field Root)) :
    MandatoryInformation Field Root :=
  let global := MandatoryInformationDerivation.close rootOf rules rules.length {}
  let rootRelative := MandatoryInformationDerivation.close rootOf rules rules.length {
    roots := MandatoryInformationDerivation.referencedRoots rootOf rules
  }
  {
    mandatory := global.fields
    mandatoryForRootGroup := rootRelative.fields
    mandatoryRootGroups := global.roots
  }

/-- Checked consumer entry for the measured fragment. Empty multi-field forms, repeatable-presence shapes outside the exact direct unindexed child, and contributing or unclassified multiple-root shapes return `none`; the exact classified cross-root no-contribution identity remains admissible. -/
def deriveCheckedMandatoryInformation [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (rules : List (MandatoryRule Field Root)) :
    Option (MandatoryInformation Field Root) :=
  if rules.all MandatoryInformationDerivation.MandatoryRule.hasNonemptyLists &&
      rules.all MandatoryInformationDerivation.MandatoryRule.hasSupportedFieldListGuardShape &&
      rules.all MandatoryInformationDerivation.MandatoryRule.hasSupportedRepeatablePresenceScope &&
      MandatoryInformationDerivation.hasSupportedNegativeFieldFormulaShape rules &&
      MandatoryInformationDerivation.hasSupportedCountShapes rules &&
      MandatoryInformationDerivation.hasSupportedCountTargetOperandShape rules &&
      MandatoryInformationDerivation.hasSupportedDeclaredFieldRequirementShape rules &&
      MandatoryInformationDerivation.hasSingleRootTopology rootOf rules then
    some (deriveMandatoryInformation rootOf rules)
  else
    none

end A12Kernel
