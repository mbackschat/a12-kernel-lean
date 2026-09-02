import A12Kernel.Semantics.NumericLiteral

/-! # Mandatory-information derivation

This module models the measured flat, nonrepeatable contributing fragment of the model-level mandatory-information service plus exact whole-rule no-contribution identities. The input retains normalized authored rule shape and the two measured declaration-derived field-required modes, including ignored WARNING and INFO severity, and the output keeps global fields, root-relative fields, and mandatory roots independent. The bounded count slice retains authored literals separately from their narrowed host values and keeps filled-count and distinct-count rules separate where their guard behavior differs. The filled-field guard slice retains existential versus universal rule identity, and finite field-guard cycles participate in the same monotone closure as acyclic chains. Exact semantic-indexed and parallel-iterated whole-rule exclusions are retained without modeling their iteration internals. Wider repetition, concrete indices, wider semantic-index shapes, filter internals, generated index rules, cross-root references, wider root topology, wider count sites, and wider Boolean formulas remain outside this carrier. -/

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

/-- Measured rule shapes that remain visible to Analyze and Explain but have no contribution in this fragment. -/
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
  deriving Repr, DecidableEq

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
  | .countLessThan fields _
  | .differentValuesLessThan fields _ => fields.map rootOf
  | .countGuardedNotFilled fields _ _ target =>
      fields.map rootOf ++ [rootOf target]
  | .differentValuesGuardedNotFilled fields _ _ target =>
      fields.map rootOf ++ [rootOf target]
  | .ignored (.fieldFilled field)
  | .ignored (.warningFieldNotFilled field)
  | .ignored (.infoFieldNotFilled field) => [rootOf field]
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields)
  | .ignored (.semanticIndexed fields)
  | .ignored (.parallelIterated fields) => fields.map rootOf
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
  | .countLessThan fields _
  | .differentValuesLessThan fields _
  | .countGuardedNotFilled fields _ _ _
  | .differentValuesGuardedNotFilled fields _ _ _ => !fields.isEmpty
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields)
  | .ignored (.semanticIndexed fields)
  | .ignored (.parallelIterated fields) => !fields.isEmpty
  | _ => true

private def MandatoryRule.hasSupportedFieldListGuardShape [DecidableEq Field] :
    MandatoryRule Field Root → Bool
  | .fieldListGuardedNotFilled premises _ _ =>
      premises.eraseDups == premises
  | _ => true

private def directFieldSeeds [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : List Field :=
  rules.foldl (fun seeds rule =>
    match rule with
    | .fieldNotFilled field => appendDistinct seeds [field]
    | _ => seeds) []

private def MandatoryRule.mentionedFields : MandatoryRule Field Root → List Field
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
  | .countLessThan fields _
  | .differentValuesLessThan fields _ => fields
  | .countGuardedNotFilled fields _ _ target => fields ++ [target]
  | .differentValuesGuardedNotFilled fields _ _ target => fields ++ [target]
  | .ignored (.fieldFilled field)
  | .ignored (.warningFieldNotFilled field)
  | .ignored (.infoFieldNotFilled field) => [field]
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields)
  | .ignored (.semanticIndexed fields)
  | .ignored (.parallelIterated fields) => fields
  | .ignored (.groupFilled _) => []

private def fieldMentionCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    (MandatoryRule.mentionedFields rule).foldl (fun count mentioned =>
      if mentioned = field then count + 1 else count) count) 0

/-- Keep the count guard on its measured shape: a duplicate-free list whose operands are direct singleton seeds or otherwise isolated, and a target mentioned only in its own guard position. Comparison truth decides contribution rather than admission; wider dependency closure stays outside this slice. -/
private def MandatoryRule.hasSupportedCountShape [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (seeds : List Field) :
    MandatoryRule Field Root → Bool
  | .countLessThan fields _
  | .differentValuesLessThan fields _ => fields.eraseDups == fields
  | .countGuardedNotFilled fields _ _ target =>
      fields.eraseDups == fields &&
        fields.all (fun field => field ∈ seeds || fieldMentionCount rules field == 1) &&
        fieldMentionCount rules target == 1
  | .differentValuesGuardedNotFilled fields comparison threshold target =>
      let thresholdValue := countThresholdValue threshold
      fields.eraseDups == fields && fields.all (· ∈ seeds) &&
        fieldMentionCount rules target == 1 && thresholdValue != -1 &&
        comparison.holds (Int.ofNat fields.length) thresholdValue
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
  | .groupNotFilled _ => true
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

/-- Checked consumer entry for the measured fragment. Empty multi-field forms and multiple or crossing roots return `none` rather than inheriting unmeasured collector behavior. -/
def deriveCheckedMandatoryInformation [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (rules : List (MandatoryRule Field Root)) :
    Option (MandatoryInformation Field Root) :=
  if rules.all MandatoryInformationDerivation.MandatoryRule.hasNonemptyLists &&
      rules.all MandatoryInformationDerivation.MandatoryRule.hasSupportedFieldListGuardShape &&
      MandatoryInformationDerivation.hasSupportedCountShapes rules &&
      MandatoryInformationDerivation.hasSupportedDeclaredFieldRequirementShape rules &&
      MandatoryInformationDerivation.hasSingleRootTopology rootOf rules then
    some (deriveMandatoryInformation rootOf rules)
  else
    none

end A12Kernel
