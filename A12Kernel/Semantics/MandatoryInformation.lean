import A12Kernel.Semantics.NumericLiteral

/-! # Mandatory-information derivation

This module models the measured flat, nonrepeatable rule fragment of the model-level mandatory-information service. The input retains the normalized rule shape, and the output keeps global fields, root-relative fields, and mandatory roots independent. The bounded count slice retains authored literals separately from their narrowed host values, and the filled-field guard slice retains existential versus universal rule identity. Repetition, concrete or semantic indices, filter internals, generated rules, cross-root references, wider root topology, cycles, wider count sites, and wider Boolean formulas remain outside this carrier. -/

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

/-- Measured count-guard spellings. The reversed inclusive form stays distinct even though it has the same numeric relation as count-on-left greater-or-equal. -/
inductive MandatoryCountGuardComparison where
  | countGreaterEqual
  | countGreater
  | literalLessEqualCount
  deriving Repr, DecidableEq

namespace MandatoryCountGuardComparison

private def holds (comparison : MandatoryCountGuardComparison)
    (count threshold : Int) : Bool :=
  match comparison with
  | .countGreaterEqual | .literalLessEqualCount => decide (threshold ≤ count)
  | .countGreater => decide (threshold < count)

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

/-- Measured rule shapes that remain visible to Analyze and Explain but have no contribution in this fragment. -/
inductive IgnoredMandatoryRule (Field Root : Type) where
  | fieldFilled (field : Field)
  | fieldsNotCollectivelyFilled (fields : List Field)
  | atLeastOneFieldFilled (fields : List Field)
  | allFieldsFilled (fields : List Field)
  | groupFilled (root : Root)
  | warningFieldNotFilled (field : Field)
  | filtered (fields : List Field)
  deriving Repr, DecidableEq

/-- Normalized, measured rule shapes for flat mandatory-information derivation. Constructors preserve the authored distinction even where two shapes have the same derived effect. -/
inductive MandatoryRule (Field Root : Type) where
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
  | .countLessThan fields _ => fields.map rootOf
  | .countGuardedNotFilled fields _ _ target =>
      fields.map rootOf ++ [rootOf target]
  | .ignored (.fieldFilled field)
  | .ignored (.warningFieldNotFilled field) => [rootOf field]
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields) => fields.map rootOf
  | .ignored (.groupFilled root) => [root]

private def MandatoryRule.apply [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (state : State Field Root) :
    MandatoryRule Field Root → State Field Root
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
  | .countLessThan fields threshold =>
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

private def fieldDependencyEdges : List (MandatoryRule Field Root) →
    List (Field × Field)
  | [] => []
  | .fieldGuardedNotFilled premise target :: rules =>
      (premise, target) :: fieldDependencyEdges rules
  | .fieldListGuardedNotFilled premises _ target :: rules =>
      premises.map (·, target) ++ fieldDependencyEdges rules
  | _ :: rules => fieldDependencyEdges rules

private def reaches [DecidableEq Field] (edges : List (Field × Field)) :
    Nat → Field → Field → Bool
  | 0, current, target => current == target
  | fuel + 1, current, target =>
      current == target || edges.any (fun (premise, successor) =>
        premise == current && reaches edges fuel successor target)

private def hasAcyclicFieldDependencies [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : Bool :=
  let edges := fieldDependencyEdges rules
  edges.all (fun (premise, target) =>
    !reaches edges edges.length target premise)

private def MandatoryRule.hasNonemptyLists : MandatoryRule Field Root → Bool
  | .disjoinedFieldNotFilled fields
  | .conjoinedFieldNotFilled fields
  | .notAllFieldsFilled fields
  | .noFieldFilled fields
  | .notExactlyOneFieldFilled fields => !fields.isEmpty
  | .fieldListGuardedNotFilled premises _ _ => !premises.isEmpty
  | .countLessThan fields _
  | .countGuardedNotFilled fields _ _ _ => !fields.isEmpty
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields) => !fields.isEmpty
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
  | .countLessThan fields _ => fields
  | .countGuardedNotFilled fields _ _ target => fields ++ [target]
  | .ignored (.fieldFilled field)
  | .ignored (.warningFieldNotFilled field) => [field]
  | .ignored (.fieldsNotCollectivelyFilled fields)
  | .ignored (.atLeastOneFieldFilled fields)
  | .ignored (.allFieldsFilled fields)
  | .ignored (.filtered fields) => fields
  | .ignored (.groupFilled _) => []

private def fieldMentionCount [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (field : Field) : Nat :=
  rules.foldl (fun count rule =>
    (MandatoryRule.mentionedFields rule).foldl (fun count mentioned =>
      if mentioned = field then count + 1 else count) count) 0

/-- Keep the count guard on its measured shape: a duplicate-free list of direct singleton seeds and a target mentioned only in its own guard position. Wider dependency closure stays outside this slice. -/
private def MandatoryRule.hasSupportedCountShape [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) (seeds : List Field) :
    MandatoryRule Field Root → Bool
  | .countLessThan fields _ => fields.eraseDups == fields
  | .countGuardedNotFilled fields comparison threshold target =>
      let thresholdValue := countThresholdValue threshold
      fields.eraseDups == fields && fields.all (· ∈ seeds) &&
        fieldMentionCount rules target == 1 &&
        (thresholdValue == -1 ||
          comparison.holds (Int.ofNat fields.length) thresholdValue)
  | _ => true

private def hasSupportedCountShapes [DecidableEq Field]
    (rules : List (MandatoryRule Field Root)) : Bool :=
  let seeds := directFieldSeeds rules
  rules.all (MandatoryRule.hasSupportedCountShape rules seeds)

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

/-- Checked consumer entry for the measured fragment. Empty multi-field forms, multiple or crossing roots, and cyclic field dependencies return `none` rather than inheriting unmeasured collector behavior. -/
def deriveCheckedMandatoryInformation [DecidableEq Field] [DecidableEq Root]
    (rootOf : Field → Root) (rules : List (MandatoryRule Field Root)) :
    Option (MandatoryInformation Field Root) :=
  if rules.all MandatoryInformationDerivation.MandatoryRule.hasNonemptyLists &&
      rules.all MandatoryInformationDerivation.MandatoryRule.hasSupportedFieldListGuardShape &&
      MandatoryInformationDerivation.hasSupportedCountShapes rules &&
      MandatoryInformationDerivation.hasSingleRootTopology rootOf rules &&
      MandatoryInformationDerivation.hasAcyclicFieldDependencies rules then
    some (deriveMandatoryInformation rootOf rules)
  else
    none

end A12Kernel
