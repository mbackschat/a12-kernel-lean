import A12Kernel.Document
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.FlatComparisonInputs
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.GroupReference
import A12Kernel.Semantics.ComputationGroupDependency

/-! # A12Kernel.Semantics.ComputationCondition — checked computation control

This module admits resolved field and group presence, ordered field-fill lists, text equality and numeric comparisons over shared arithmetic trees, ordered `And`/`Or`, common-precondition expansion and first-match selection at one target instance. An absent row precondition selects directly; model-level certification keeps that source shape to a sole alternative even though composed tables may later contain it beside other rows. The selector separates clean not-true and no-match from an invalid cell actually read as poison. Numeric atoms retain field metadata or structural row bindings; checked consumers propagate a reached binding error outside semantic poison. Other predicate families, operation evaluation and model-level alternative legality remain separate clauses.
-/

namespace A12Kernel

/-- Pure checked-cell reads plus the optional explicit evaluation world shared by scalar computation fragments. Model and path checking remain outside this context; a clock-dependent checked expression fails structurally when `world` is absent. -/
structure ScalarComputationContext where
  read : FieldId → CheckedCell
  storedText : FieldId → Option String := fun _ => none
  /-- Regime-selected Number text for String coercion; supplied by the checked document. -/
  numberText : FieldId → Option String := fun _ => none
  world : Option World := none
  /-- The repeatable target row being computed, empty for a fixed target. Only a structural
  `CurrentRepetition` operand reads it; every field read is already addressed by `read`. -/
  row : Env := []
  addressed : Option ComputationFillContext := none

/-- Apply fixed-target overrides to both cell read channels, discarding stale source text. Group guards and expanded fill lists
use addressed reads, so they must share the pending/completed policy of direct operands;
ordinary fields retain their original environment-sensitive reader. Number formal text is a separate
channel from stored spelling because spec/04 selects it by input regime. -/
def ScalarComputationContext.withFixedOverlay
    (context : ScalarComputationContext) (overlay : FieldId → Option CheckedCell)
    (stored : FieldId → Option String := fun _ => none)
    (formalNumberText : FieldId → Option String := fun _ => none) :
    ScalarComputationContext :=
  { context with
    read := fun field => (overlay field).getD (context.read field)
    storedText := fun field => if (overlay field).isSome then stored field else context.storedText field
    numberText := fun field => if (overlay field).isSome then formalNumberText field else context.numberText field
    addressed := context.addressed.map fun addressed =>
      { addressed with
        read := fun row field => (overlay field).getD (addressed.read row field)
        storedText := fun row field => if (overlay field).isSome then stored field else addressed.storedText row field
        numberText := fun row field => if (overlay field).isSome then formalNumberText field else addressed.numberText row field } }

/-- Supply the explicit evaluation world without changing the checked-cell read policy. -/
def ScalarComputationContext.withWorld
    (context : ScalarComputationContext) (world : World) :
    ScalarComputationContext :=
  { context with world := some world }

/-- Guard failures retain structural context errors outside semantic poison. -/
inductive ComputationConditionError where
  | binding (error : EnvBindingError)
  | fieldFill (error : ComputationFillError)
  | groupContextRequired
  deriving Repr, DecidableEq

/-- Scalar Number reads and structural coordinates share the ordinary arithmetic tree in guards. -/
inductive ComputationNumericAtom where
  | field (source : FlatNumberField)
  | repetition (source : BoundCurrentRepetitionSource)
  | baseYear (year : Int)
  deriving Repr, DecidableEq

def ComputationNumericAtom.referencesField : ComputationNumericAtom → FieldId → Bool
  | .field source, target => source.id == target
  | .repetition _, _ | .baseYear _, _ => false

def ComputationNumericAtom.summary : ComputationNumericAtom → NumericScaleSummary
  | .field source => .field source.info.scale
  | .repetition _ | .baseYear _ => .field 0

/-- Missing row coordinates remain structural failures, separate from reached cell poison. -/
def ComputationNumericAtom.read (context : ScalarComputationContext) :
    ComputationNumericAtom → Except EnvBindingError NumericComputationResult
  | .field source =>
      pure (match ({ read := context.read } : FlatContext).resolveNumberComparisonOperandAt
          .computation source with
        | .value amount _ => .value amount
        | .unknown cause => .poison cause)
  | .repetition source => do pure (.value (← source.coordinateAt context.row))
  | .baseYear year => pure (.value year)

/-- Singular presence and an ordinary group-list operand can read the same content but have
separate target and scheduling rules (spec/09, containing-group review grid 2026-10-03). -/
inductive ComputationGroupDependencyKind where
  | conditionalPresence
  | ordinaryList
  deriving Repr, DecidableEq

/-- A group guard preserves authored identity and complete operand membership separately from
its runtime content slice. Elaboration certifies all three against the same model. -/
structure ComputationGroupOperand where
  reference : ResolvedGroupReference
  content : ResolvedComputationGroupSource
  members : List FieldId
  starPath : Option StarPath := none
  dependencyKind : ComputationGroupDependencyKind := .conditionalPresence
  deriving Repr, DecidableEq

/-- Atomic leaves of the parser-independent computation-condition fragment. -/
inductive ComputationConditionLeaf (Atom : Type := ComputationNumericAtom) (Predicate : Type := Empty) where
  | fieldFilled (field : FieldId)
  | fieldNotFilled (field : FieldId)
  | numeric (comparison : NumericComparisonOf Atom)
  | predicate (source : Predicate)
  /-- The certifier restricts this shared comparison carrier to String/Enumeration forms. -/
  | text (comparison : FlatComparison)
  /-- Boolean/Confirm scalar comparisons retain their distinct empty policies. -/
  | scalar (comparison : FlatComparison)
  | fieldFill (operator : FieldFillQuantifier) (sources : List ComputationFillSource)
  | groupPresence (operator : GroupPresenceOperator) (source : ComputationGroupOperand)
  deriving Repr, DecidableEq

def ComputationConditionLeaf.groupReference? :
    ComputationConditionLeaf Atom Predicate → Option (GroupPresenceOperator × ResolvedGroupReference)
  | .groupPresence operator source => match source.dependencyKind with
      | .conditionalPresence => some (operator, source.reference)
      | .ordinaryList => none
  | _ => none

/-- Computation control reuses the common checked connective tree; its phase-specific leaves and result projection differ from validation. -/
abbrev ComputationConditionOf (Atom : Type) (Predicate : Type := Empty) :=
  ConditionTree (ComputationConditionLeaf Atom Predicate)

abbrev ComputationCondition := ComputationConditionOf ComputationNumericAtom

namespace CellObservation

/-- Consume one computation-phase observation as `FieldFilled`. The method is shared by direct fields and already-resolved indexed reads. -/
@[simp]
def evalComputationFilled : CellObservation → ComputationConditionResult
  | .empty => .notTrue
  | .value _ => .holds
  | .unknown cause => .poison cause
  | .poison cause => .poison cause

/-- Consume one computation-phase observation as `FieldNotFilled`. Clean truth reverses, while a reached formal cause remains poison. -/
@[simp]
def evalComputationNotFilled : CellObservation → ComputationConditionResult
  | .empty => .holds
  | .value _ => .notTrue
  | .unknown cause => .poison cause
  | .poison cause => .poison cause

end CellObservation

namespace ComputationConditionOf

/-- Numeric leaves supply their structural inventory; primitive identities remain unchanged. -/
def referencesFieldWith (condition : ComputationConditionOf Atom Predicate)
    (references : Atom → FieldId → Bool) (predicateReferences : Predicate → FieldId → Bool)
    (target : FieldId) : Bool :=
  condition.anyLeaf fun
    | .predicate source => predicateReferences source target
    | .fieldFilled field | .fieldNotFilled field => field == target
    | .fieldFill _ sources => sources.any (·.field == target)
    | .groupPresence _ source => source.members.contains target
    | .text comparison | .scalar comparison => comparison.fieldIds.contains target
    | .numeric comparison => comparison.left.anyAtom (fun atom => references atom target) ||
        comparison.right.anyAtom (fun atom => references atom target)

def forbidsTargetWith (condition : ComputationConditionOf Atom Predicate)
    (references : Atom → FieldId → Bool) (predicateReferences : Predicate → FieldId → Bool)
    (target : FieldId) : Bool :=
  match condition with
  | .leaf (.groupPresence .filled source) =>
      match source.dependencyKind with
      | .conditionalPresence => false
      | .ordinaryList => source.members.contains target
  | .and left right | .or left right =>
      forbidsTargetWith left references predicateReferences target || forbidsTargetWith right references predicateReferences target
  | leaf => referencesFieldWith leaf references predicateReferences target

def requiresProducerWith (condition : ComputationConditionOf Atom Predicate)
    (references : Atom → FieldId → Bool) (predicateReferences : Predicate → FieldId → Bool)
    (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  match condition with
  | .leaf (.groupPresence operator source) =>
      let member := source.members.contains producer
      let conditional := source.dependencyKind == .conditionalPresence &&
        operator == .filled && source.members.contains consumer
      ComputationGroupDependency.requiresProducer (member && !conditional)
        (member && conditional) (consumer == producer) (producerProtected source.reference)
  | .and left right | .or left right =>
      requiresProducerWith left references predicateReferences consumer producer producerProtected ||
        requiresProducerWith right references predicateReferences consumer producer producerProtected
  | leaf => referencesFieldWith leaf references predicateReferences producer

end ComputationConditionOf

namespace ComputationCondition

abbrev fieldFilled (field : FieldId) : ComputationCondition :=
  .leaf (.fieldFilled field)

abbrev fieldNotFilled (field : FieldId) : ComputationCondition :=
  .leaf (.fieldNotFilled field)

abbrev and (left right : ComputationCondition) : ComputationCondition :=
  ConditionTree.and left right

abbrev or (left right : ComputationCondition) : ComputationCondition :=
  ConditionTree.or left right

/-- Group-list predicates compose each entity's own positive and negative presence tests.
The source expansion uses the same structure (`ExpandService.expandAndCreate`); retaining the
leaves preserves runtime content reads; each leaf separately retains whether its authored
shape permits conditional dependencies, since target checking precedes this expansion. -/
def ofGroupListWith (operator : GroupFillQuantifier)
    (first : ComputationConditionOf Atom Predicate × ComputationConditionOf Atom Predicate)
    (rest : List (ComputationConditionOf Atom Predicate × ComputationConditionOf Atom Predicate)) : ComputationConditionOf Atom Predicate :=
  let positives (join : ComputationConditionOf Atom Predicate → ComputationConditionOf Atom Predicate → ComputationConditionOf Atom Predicate) :=
    rest.foldl (fun accumulated next => join accumulated next.1) first.1
  let negatives (join : ComputationConditionOf Atom Predicate → ComputationConditionOf Atom Predicate → ComputationConditionOf Atom Predicate) :=
    rest.foldl (fun accumulated next => join accumulated next.2) first.2
  match operator with
  | .allGroupsFilled => positives .and
  | .noGroupFilled => negatives .and
  | .atLeastOneGroupFilled => positives .or
  | .notAllGroupsFilled => negatives .or
  | .groupsNotCollectivelyFilled => .and (positives .or) (negatives .or)

def ofGroupList (operator : GroupFillQuantifier)
    (first : ComputationCondition × ComputationCondition)
    (rest : List (ComputationCondition × ComputationCondition)) : ComputationCondition :=
  ofGroupListWith operator first rest

/-- Complete operand membership, including a target contained by its positive group guard.
Static target bans and conditional scheduling use separate queries. -/
def referencesField (condition : ComputationCondition) (target : FieldId) : Bool :=
  ComputationConditionOf.referencesFieldWith condition ComputationNumericAtom.referencesField
    (fun source => nomatch source) target

/-- The positive ancestor-group carve-out changes the target ban, not operand membership
([`spec/09`](../../spec/09-computations.md) §5). Other reads keep their complete structural inventory. -/
def forbidsTarget (condition : ComputationCondition) (target : FieldId) : Bool :=
  ComputationConditionOf.forbidsTargetWith condition ComputationNumericAtom.referencesField
    (fun source => nomatch source) target

/-- Preserve ordinary dependencies while consulting the producer profile only for a positive
containing-group read. The complete operand inventory remains available in `referencesField`. -/
def requiresProducer (condition : ComputationCondition) (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  ComputationConditionOf.requiresProducerWith condition ComputationNumericAtom.referencesField
    (fun source => nomatch source) consumer producer producerProtected

/-- Group content uses the addressed overlay whenever topology is needed. A missing overlay is
structural failure, never evidence that no descendant row exists. -/
def evalGroupPresence (operator : GroupPresenceOperator) (source : ComputationGroupOperand)
    (context : ScalarComputationContext) : Except ComputationConditionError ComputationConditionResult :=
  match context.addressed with
  | some addressed => do
      match source.starPath with
      | none => (source.content.eval operator addressed.document addressed.read context.row).mapError .binding
      | some path =>
          let resolved ← (path.resolveInCapacity addressed.document context.row).mapError
            (ComputationConditionError.fieldFill ∘ ComputationFillError.addressing)
          let instances ← resolved.environments.mapM fun environment =>
            (source.content.eval .filled addressed.document addressed.read environment).mapError .binding
          let present := instances.any (· == .holds)
          pure (if (match operator with | .filled => present | .notFilled => !present)
            then .holds else .notTrue)
  | none =>
      if source.content.rowLevels.isEmpty then
        (source.content.eval operator { instantiatedRows := [], rawCells := fun _ => none }
          (fun _ => context.read) context.row).mapError .binding
      else .error .groupContextRequired

/-- Evaluate `FieldFilled` for one resolved checked field. A clean value counts as filled regardless of its scalar value; ordinary formal invalidity is poison rather than filled or empty. -/
def evalFieldFilled (context : ScalarComputationContext)
    (field : FieldId) : ComputationConditionResult :=
  (observeCell .computation (context.read field)).evalComputationFilled

/-- Equality consumes typed operands after their phase-specific reads. Unavailability precedes
empty comparison suppression, shared by token and Boolean/Confirm comparisons. -/
def evalSimpleEquality [BEq α] (op : EqualityOp)
    (left right : SimpleComparisonOperand α) : ComputationConditionResult :=
  evalComputationComparison (fun left right => op.holds (left == right)) left right

/-- Evaluate a checked simple comparison through the shared phase-aware operand fold. -/
def evalSimpleComparison (comparison : FlatComparison)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  let read := fun field => Except.ok (ε := Empty) (context.read field)
  match comparison.foldSimpleReads .computation read read evalComputationComparisonExcept context.world with
  | none => .notTrue
  | some (.ok result) => result
  | some (.error impossible) => nomatch impossible

/-- Boolean and Confirm guards retain their distinct empty policies through the shared operand fold. -/
def evalScalarComparison (comparison : FlatComparison)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  match comparison with
  | .boolean _ _ _ | .confirm _ _ => evalSimpleComparison comparison context
  | _ => .notTrue

/-- Text guards reuse declaration-checked projections and preserve poison before empty suppression
(spec/02; src-text-computation-guards). -/
def evalTextComparison (comparison : FlatComparison)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  match comparison with
  | .string _ _ _ | .enumeration _ _ _ | .textFields _ _ _ => evalSimpleComparison comparison context
  | _ => .notTrue

/-- Resolve the ordered list against the current overlay before applying the shared fill scan. -/
def evalFieldFill (operator : FieldFillQuantifier) (sources : List ComputationFillSource)
    (context : ScalarComputationContext) : Except ComputationFillError ComputationConditionResult := do
  let slots ← sources.mapM (·.slots context.read context.row context.addressed)
  pure (operator.evalComputation slots.flatten)

end ComputationCondition

namespace ComputationConditionOf

/-- Preserve every primitive guard while changing only its numeric source representation. -/
def mapNumericM (transform : Atom → Except Error Other)
    (predicate : Predicate → Except Error OtherPredicate) :
    ComputationConditionOf Atom Predicate → Except Error (ComputationConditionOf Other OtherPredicate)
  | .leaf (.numeric comparison) => do
      let left ← comparison.left.mapM transform
      let right ← comparison.right.mapM transform
      pure (.leaf (.numeric { comparison with left, right }))
  | .leaf (.predicate source) => (.leaf ∘ .predicate) <$> predicate source
  | .leaf (.fieldFilled field) => pure (.leaf (.fieldFilled field))
  | .leaf (.fieldNotFilled field) => pure (.leaf (.fieldNotFilled field))
  | .leaf (.text comparison) => pure (.leaf (.text comparison))
  | .leaf (.scalar comparison) => pure (.leaf (.scalar comparison))
  | .leaf (.fieldFill operator sources) => pure (.leaf (.fieldFill operator sources))
  | .leaf (.groupPresence operator source) => pure (.leaf (.groupPresence operator source))
  | .and left right => do pure (.and (← mapNumericM transform predicate left) (← mapNumericM transform predicate right))
  | .or left right => do pure (.or (← mapNumericM transform predicate left) (← mapNumericM transform predicate right))

/-- All checked source families share the ordered connective and numeric comparison owners.
The reader retains its typed atom and structural error; it cannot certify an unchecked leaf. -/
def evalCheckedWith (condition : ComputationConditionOf Atom Predicate) (context : ScalarComputationContext)
    (primitiveError : ComputationConditionError → Error)
    (read : Atom → Except Error NumericComputationResult)
    (evaluatePredicate : Predicate → Except Error ComputationConditionResult) :
    Except Error ComputationConditionResult :=
  condition.evalComputationExcept fun
    | .numeric comparison => comparison.evalComputationWith read
    | .predicate source => evaluatePredicate source
    | .fieldFilled field => pure (ComputationCondition.evalFieldFilled context field)
    | .fieldNotFilled field => pure ((observeCell .computation (context.read field)).evalComputationNotFilled)
    | .text comparison => pure (ComputationCondition.evalTextComparison comparison context)
    | .scalar comparison => pure (ComputationCondition.evalScalarComparison comparison context)
    | .fieldFill operator sources =>
        (ComputationCondition.evalFieldFill operator sources context).mapError (primitiveError ∘ .fieldFill)
    | .groupPresence operator source =>
        (ComputationCondition.evalGroupPresence operator source context).mapError primitiveError

def withCommon (common own : Option (ComputationConditionOf Atom Predicate)) :
    Option (ComputationConditionOf Atom Predicate) :=
  match common, own with
  | none, own => own
  | some common, none => some common
  | some common, some own => some (.and common own)

end ComputationConditionOf

namespace ComputationCondition

/-- Evaluate a resolved leaf through computation-phase reads; the pure compatibility entry assumes its row context is complete. -/
def ComputationConditionLeaf.eval (context : ScalarComputationContext)
    (leaf : ComputationConditionLeaf) : ComputationConditionResult :=
  (ComputationConditionOf.evalCheckedWith (.leaf leaf) context id
    (fun atom => (atom.read context).mapError ComputationConditionError.binding)
    (fun source => nomatch source)).toOption.getD .notTrue

/-- Evaluate a computation condition left-to-right. `And` stops on clean not-true, `Or` stops on clean holds, and a poison already read aborts without consulting the remaining operand. -/
def eval (condition : ComputationCondition)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  condition.evalComputation (ComputationConditionLeaf.eval context)

/-- Checked consumers retain coordinate failures instead of the low-level evaluator's
non-holding fallback for a context outside its row contract. -/
def evalChecked (condition : ComputationCondition) (context : ScalarComputationContext) :
    Except ComputationConditionError ComputationConditionResult :=
  ComputationConditionOf.evalCheckedWith condition context id
    (fun atom => (atom.read context).mapError .binding) (fun source => nomatch source)

theorem evalChecked_and (context : ScalarComputationContext) (left right : ComputationCondition) :
    (and left right).evalChecked context = match left.evalChecked context with
      | .error error => .error error
      | .ok .holds => right.evalChecked context
      | .ok .notTrue => .ok .notTrue
      | .ok (.poison cause) => .ok (.poison cause) := by
  change (do
    match ← left.evalChecked context with
    | .holds => right.evalChecked context
    | .notTrue => pure .notTrue
    | .poison cause => pure (.poison cause)) = _
  cases h : left.evalChecked context with
  | error error => rfl
  | ok result => cases result <;> rfl

@[simp]
theorem eval_fieldFilled (context : ScalarComputationContext) (field : FieldId) :
    (fieldFilled field).eval context = evalFieldFilled context field := by
  rfl

@[simp]
theorem eval_fieldNotFilled (context : ScalarComputationContext) (field : FieldId) :
    (fieldNotFilled field).eval context =
      (observeCell .computation (context.read field)).evalComputationNotFilled := by
  rfl

@[simp]
theorem eval_and (context : ScalarComputationContext)
    (left right : ComputationCondition) :
    (and left right).eval context =
      match left.eval context with
      | .holds => right.eval context
      | .notTrue => .notTrue
      | .poison cause => .poison cause := by
  rfl

@[simp]
theorem eval_or (context : ScalarComputationContext)
    (left right : ComputationCondition) :
    (or left right).eval context =
      match left.eval context with
      | .holds => .holds
      | .notTrue => right.eval context
      | .poison cause => .poison cause := by
  rfl

end ComputationCondition



/-- One ordered computation alternative. An absent precondition selects its operation directly without fabricating a field read; the payload remains unevaluated during selection. -/
structure ComputationAlternative (Operation : Type) (Guard : Type := ComputationCondition) where
  precondition : Option Guard := none
  operation : Operation
  deriving Repr, DecidableEq

/-- Result of scanning computation alternatives in declaration order. No-match is clean absence; poison records the first invalid read reached before any selection. -/
inductive ComputationAlternativeSelection (Operation : Type) where
  | noMatch
  | selected (operation : Operation)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- One alternative's guard with an optional whole-computation precondition joined on. A present
common guard is the left operand so clean false and poison decide before the alternative-specific
guard. -/
def ComputationCondition.withCommon (commonPrecondition own : Option ComputationCondition) :
    Option ComputationCondition :=
  ComputationConditionOf.withCommon commonPrecondition own

namespace ComputationAlternative

/-- Expand an optional whole-computation precondition into the existing guarded alternative core,
joining it onto every alternative's guard by `ComputationCondition.withCommon`. -/
def expandCommonPrecondition
    (commonPrecondition : Option ComputationCondition)
    (alternatives : List (ComputationAlternative Operation)) :
    List (ComputationAlternative Operation) :=
  match commonPrecondition with
  | none => alternatives
  | some common =>
      alternatives.map fun alternative => {
        precondition := ComputationCondition.withCommon (some common) alternative.precondition
        operation := alternative.operation }

/-- One ordered scan shared by pure and structurally checked guard evaluation. -/
def selectFirstWith [Monad m]
    (evaluate : Guard → m ComputationConditionResult)
    (alternatives : List (ComputationAlternative Operation Guard)) :
    m (ComputationAlternativeSelection Operation) :=
  match alternatives with
  | [] => pure .noMatch
  | alternative :: remaining => do
      match alternative.precondition with
      | none => pure (.selected alternative.operation)
      | some precondition =>
          match ← evaluate precondition with
          | .holds => pure (.selected alternative.operation)
          | .notTrue => selectFirstWith evaluate remaining
          | .poison cause => pure (.poison cause)

/-- Select the first holding alternative through the pure computation evaluator. -/
def selectFirst (alternatives : List (ComputationAlternative Operation))
    (context : ScalarComputationContext) : ComputationAlternativeSelection Operation :=
  Id.run (selectFirstWith (m := Id) (fun condition => condition.eval context) alternatives)

@[simp] theorem selectFirst_nil (context : ScalarComputationContext) :
    selectFirst ([] : List (ComputationAlternative Operation)) context = .noMatch := rfl

/-- The pure specialization retains the original one-step scan equation. -/
theorem selectFirst_cons (head : ComputationAlternative Operation)
    (tail : List (ComputationAlternative Operation)) (context : ScalarComputationContext) :
    selectFirst (head :: tail) context = match head.precondition with
      | none => .selected head.operation
      | some precondition => match precondition.eval context with
        | .holds => .selected head.operation
        | .notTrue => selectFirst tail context
        | .poison cause => .poison cause := by
  cases h : head.precondition with
  | none => simp [selectFirst, selectFirstWith, h, Id.run] <;> rfl
  | some guard =>
      cases hg : guard.eval context <;> simp [selectFirst, selectFirstWith, h, hg, Id.run] <;> rfl

/-- The checked selector preserves a guard's structural coordinate failure. -/
def selectFirstChecked (alternatives : List (ComputationAlternative Operation))
    (context : ScalarComputationContext) :
    Except ComputationConditionError (ComputationAlternativeSelection Operation) :=
  selectFirstWith (fun condition => condition.evalChecked context) alternatives

@[simp] theorem selectFirstChecked_nil (context : ScalarComputationContext) :
    selectFirstChecked ([] : List (ComputationAlternative Operation)) context = .ok .noMatch := rfl

theorem selectFirstChecked_cons (head : ComputationAlternative Operation)
    (tail : List (ComputationAlternative Operation)) (context : ScalarComputationContext) :
    selectFirstChecked (head :: tail) context = match head.precondition with
      | none => .ok (.selected head.operation)
      | some guard => match guard.evalChecked context with
        | .error error => .error error
        | .ok .holds => .ok (.selected head.operation)
        | .ok .notTrue => selectFirstChecked tail context
        | .ok (.poison cause) => .ok (.poison cause) := by
  cases h : head.precondition with
  | none => simp [selectFirstChecked, selectFirstWith, h] <;> rfl
  | some guard =>
      cases hg : guard.evalChecked context with
      | error error => simp [selectFirstChecked, selectFirstWith, h, hg] <;> rfl
      | ok result => cases result <;> simp [selectFirstChecked, selectFirstWith, h, hg] <;> rfl

end ComputationAlternative

end A12Kernel
