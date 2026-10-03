import A12Kernel.Document
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.ComputationCondition — checked computation control

This module admits resolved field presence, ordered field-fill lists, text equality and numeric comparisons over shared arithmetic trees, ordered `And`/`Or`, common-precondition expansion and first-match selection at one target instance. An absent row precondition selects directly; model-level certification keeps that source shape to a sole alternative even though composed tables may later contain it beside other rows. The selector separates clean not-true and no-match from an invalid cell actually read as poison. Numeric atoms retain field metadata or structural row bindings; checked consumers propagate a reached binding error outside semantic poison. Other predicate families, operation evaluation and model-level alternative legality remain separate clauses.
-/

namespace A12Kernel

/-- Pure checked-cell reads plus the optional explicit evaluation world shared by scalar computation fragments. Model and path checking remain outside this context; a clock-dependent checked expression fails structurally when `world` is absent. -/
structure ScalarComputationContext where
  read : FieldId → CheckedCell
  world : Option World := none
  /-- The repeatable target row being computed, empty for a fixed target. Only a structural
  `CurrentRepetition` operand reads it; every field read is already addressed by `read`. -/
  row : Env := []
  addressed : Option ComputationFillContext := none

/-- Supply the explicit evaluation world without changing the checked-cell read policy. -/
def ScalarComputationContext.withWorld
    (context : ScalarComputationContext) (world : World) :
    ScalarComputationContext :=
  { context with world := some world }

/-- Guard failures retain structural context errors outside semantic poison. -/
inductive ComputationConditionError where
  | binding (error : EnvBindingError)
  | fieldFill (error : ComputationFillError)
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

/-- Atomic leaves of the parser-independent computation-condition fragment. -/
inductive ComputationConditionLeaf where
  | fieldFilled (field : FieldId)
  | fieldNotFilled (field : FieldId)
  | numeric (comparison : NumericComparisonOf ComputationNumericAtom)
  /-- The certifier restricts this shared comparison carrier to String/Enumeration forms. -/
  | text (comparison : FlatComparison)
  | fieldFill (operator : FieldFillQuantifier) (sources : List ComputationFillSource)
  deriving Repr, DecidableEq

/-- Computation control reuses the common checked connective tree; its phase-specific leaves and result projection differ from validation. -/
abbrev ComputationCondition := ConditionTree ComputationConditionLeaf

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

namespace ComputationCondition

abbrev fieldFilled (field : FieldId) : ComputationCondition :=
  .leaf (.fieldFilled field)

abbrev fieldNotFilled (field : FieldId) : ComputationCondition :=
  .leaf (.fieldNotFilled field)

abbrev and (left right : ComputationCondition) : ComputationCondition :=
  ConditionTree.and left right

abbrev or (left right : ComputationCondition) : ComputationCondition :=
  ConditionTree.or left right

/-- Whether the resolved condition mentions one exact field. This structural query is shared by checked table construction and generated-validation lowering. -/
def referencesField (condition : ComputationCondition) (target : FieldId) : Bool :=
  match condition with
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) => field == target
  | .leaf (.fieldFill _ sources) => sources.any (·.field == target)
  | .leaf (.text comparison) => comparison.fieldIds.contains target
  | .leaf (.numeric comparison) =>
      comparison.left.anyAtom (·.referencesField target) ||
        comparison.right.anyAtom (·.referencesField target)
  | .and left right | .or left right =>
      left.referencesField target || right.referencesField target

/-- Evaluate `FieldFilled` for one resolved checked field. A clean value counts as filled regardless of its scalar value; ordinary formal invalidity is poison rather than filled or empty. -/
def evalFieldFilled (context : ScalarComputationContext)
    (field : FieldId) : ComputationConditionResult :=
  (observeCell .computation (context.read field)).evalComputationFilled

/-- Text guards reuse declaration-checked projections. Formal unavailability dominates an empty
partner, as measured by the empty-before-invalid rows in `src-text-computation-guards`. -/
def evalTextComparison (comparison : FlatComparison)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  let read (operand : FlatTextFieldOperand) : SimpleComparisonOperand String :=
    match operand.checkedValueListCellAt .computation (context.read operand.field.id) with
    | .empty => .notEvaluated
    | .present value => .value value true
    | .unknown cause => .unknown cause
  let compare (op : EqualityOp) (left right : SimpleComparisonOperand String) :=
    match left, right with
    | .unknown cause, _ | _, .unknown cause => ComputationConditionResult.poison cause
    | .notEvaluated, _ | _, .notEvaluated => .notTrue
    | .value left _, .value right _ => if op.holds (left == right) then .holds else .notTrue
  match comparison with
  | .string op field expected => compare op (read (.string field))
      (if expected.isEmpty then .notEvaluated else .value expected true)
  | .enumeration op operand expected => compare op (read (.enumeration operand)) (.value expected true)
  | .textFields op left right => compare op (read left) (read right)
  | _ => .notTrue

/-- Resolve the ordered list against the current overlay before applying the shared fill scan. -/
def evalFieldFill (operator : FieldFillQuantifier) (sources : List ComputationFillSource)
    (context : ScalarComputationContext) : Except ComputationFillError ComputationConditionResult := do
  let slots ← sources.mapM (·.slots context.read context.row context.addressed)
  pure (operator.evalComputation slots.flatten)

/-- Evaluate a resolved leaf through computation-phase reads; the pure compatibility entry assumes its row context is complete. -/
def ComputationConditionLeaf.eval (context : ScalarComputationContext) :
    ComputationConditionLeaf → ComputationConditionResult
  | .fieldFilled field => evalFieldFilled context field
  | .fieldNotFilled field =>
      (observeCell .computation (context.read field)).evalComputationNotFilled
  | .text comparison => evalTextComparison comparison context
  | .fieldFill operator sources =>
      (evalFieldFill operator sources context).toOption.getD .notTrue
  | .numeric comparison =>
      (comparison.evalComputationWith (ComputationNumericAtom.read context)).toOption.getD .notTrue

/-- Evaluate a computation condition left-to-right. `And` stops on clean not-true, `Or` stops on clean holds, and a poison already read aborts without consulting the remaining operand. -/
def eval (condition : ComputationCondition)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  condition.evalComputation (ComputationConditionLeaf.eval context)

/-- Checked consumers retain coordinate failures instead of the low-level evaluator's
non-holding fallback for a context outside its row contract. -/
def evalChecked (condition : ComputationCondition) (context : ScalarComputationContext) :
    Except ComputationConditionError ComputationConditionResult :=
  condition.evalComputationExcept fun
    | .numeric comparison =>
        (comparison.evalComputationWith (ComputationNumericAtom.read context)).mapError .binding
    | .fieldFill operator sources => (evalFieldFill operator sources context).mapError .fieldFill
    | leaf => pure (ComputationConditionLeaf.eval context leaf)

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
structure ComputationAlternative (Operation : Type) where
  precondition : Option ComputationCondition := none
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
  match commonPrecondition, own with
  | none, own => own
  | some common, none => some common
  | some common, some own => some (.and common own)

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
    (evaluate : ComputationCondition → m ComputationConditionResult)
    (alternatives : List (ComputationAlternative Operation)) :
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
