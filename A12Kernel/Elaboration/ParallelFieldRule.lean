import A12Kernel.Elaboration.CustomCondition
import A12Kernel.Elaboration.ParallelFieldPair
import A12Kernel.Elaboration.ParallelInstanceView
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Elaboration.IterationGuard
import A12Kernel.Elaboration.ErrorTargetDeclaration
import A12Kernel.Elaboration.NumericAggregate.Fields
import A12Kernel.Elaboration.TemporalNumericInput

/-! # Parallel validation over one checked field/group pair

The pair owns key identity, optional physical rows and error projection. Field leaves retain the existing scalar consumers; group leaves reuse resolved group content after index availability. A custom-condition leaf reads no field and guards no iteration; its callback receives the same invocation channels as the ordinary carrier, with the error pointer taken at the joined row. Topology anchors never count as authored references. See spec/07 §2 and the parallel-group-outer source checkpoint.
-/

namespace A12Kernel

inductive ParallelFieldSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq

/-- Anchors preserve the small pair API; explicit declarations retain every authored payload and
bound scalar read independently of the topology anchors (spec/07 parallel iteration). -/
inductive ParallelFieldOperand where
  | left
  | right
  | field (declaration : FlatFieldDecl)
  deriving Repr, DecidableEq

/-- One numeric comparison operand over the joined rows: a Number field, a numeric component of a temporal field, or a fixed list of Number fields. Each keeps the ordinary validation atom's fold; the kind-specific declarations are recovered from the pair, so a payload of the wrong kind fails admission rather than evaluation. An ordinary atom, such as a starred aggregate, reads no joined field and keeps its ordinary meaning at the common outer row (generated rule of the joined-carrier capture's row `j11`, 2026-10-14). -/
inductive ParallelNumericAtomOf (Field Ordinary : Type) where
  | field (operand : Field)
  | temporalPart (operand : Field) (part : TemporalNumericPart)
  | aggregate (op : NumericAggregateOp) (operands : List Field)
  | ordinary (atom : Ordinary)
  deriving Repr, DecidableEq

namespace ParallelNumericAtomOf

/-- Every joined field the atom reads, in authored order. -/
def operands : ParallelNumericAtomOf Field Ordinary → List Field
  | .field operand | .temporalPart operand _ => [operand]
  | .aggregate _ operands => operands
  | .ordinary _ => []

def mapM [Monad m] (bind : Field → m Target) (bindOrdinary : Ordinary → m Ordinary') :
    ParallelNumericAtomOf Field Ordinary → m (ParallelNumericAtomOf Target Ordinary')
  | .field operand => .field <$> bind operand
  | .temporalPart operand part => (.temporalPart · part) <$> bind operand
  | .aggregate op operands => .aggregate op <$> operands.mapM bind
  | .ordinary atom => .ordinary <$> bindOrdinary atom

end ParallelNumericAtomOf

inductive ParallelFieldLeafOf (Field Ordinary Atom : Type) where
  | groupPresence (op : GroupPresenceOperator) (reference : ResolvedGroupReference)
  | presence (side : Field) (op : RepeatableFieldPresenceOperator)
  | numeric (op : NumericComparisonOp) (left right : Field)
  | fill (op : FieldFillQuantifier) (left right : Field)
  | comparison (value : NumericComparisonOf (ParallelNumericAtomOf Field Atom))
  | customCondition (name : CheckedCustomConditionName)
  /-- `FieldValuesNotUnique` over two or more direct String or Enumeration fields of the joined row
  (joined-carrier-limits capture, row `d04`, 2026-10-14). -/
  | valuesNotUnique (operands : List Field)
  /-- An ordinary flat leaf elaborated against the joined-instance view, where each pair group reads
  one row. `reads` lists the fields it reads, so admission and references see them as payloads. -/
  | flat (condition : FlatConditionLeaf) (reads : List Field)
  /-- A model-checked leaf the instance view has no flat form for, such as a starred or filtered
  aggregate, a keyed read or a pattern test. It means what the ordinary carrier means at its
  [binding](A12Kernel.ParallelOrdinaryBinding) (keyed-membership capture, rows `p00`–`p02` and
  `RPk`, 2026-10-13; joined-carrier capture, rows `k01`–`k09` and the generated rules of
  `j03`–`j10`, 2026-10-14). -/
  | ordinary (leaf : Ordinary)

/-- An ordinary comparison atom is carried by its one-atom comparison leaf `atom > 0`, checked by the
ordinary reader, so binding, admission and references answer for it as for an ordinary leaf. -/
abbrev ParallelFieldLeaf (model : FlatModel) :=
  ParallelFieldLeafOf ParallelFieldOperand (ValidationConditionLeaf model) (ValidationConditionLeaf model)

/-- A pair comparison atom of `model`. -/
abbrev ParallelNumericAtom (model : FlatModel) :=
  ParallelNumericAtomOf ParallelFieldOperand (ValidationConditionLeaf model)

/-- The numeric atom an ordinary comparison atom's leaf compares. -/
def ValidationConditionLeaf.orderedAtom? : ValidationConditionLeaf model → Option (OrderedNumericValidationAtom model)
  | .orderedNumeric _ { left := .atom atom, .. } => some atom
  | _ => none

abbrev ParallelFieldCondition (model : FlatModel) := ConditionTree (ParallelFieldLeaf model)

def CheckedParallelFieldPair.declaration (pair : CheckedParallelFieldPair model) :
    ParallelFieldOperand → FlatFieldDecl
  | .left => pair.leftDeclaration
  | .right => pair.rightDeclaration
  | .field declaration => declaration

/-- Where an ordinary leaf beside the join is evaluated. The common outer binding is preferred; a
leaf whose iterating reads it does not fix, a key field on one side's row for instance, reads that
side's joined row, the error side's first. -/
inductive ParallelOrdinaryBinding where
  | common
  | side (side : ParallelFieldSide)
  deriving Repr, DecidableEq

/-- The binding that fixes every iterating read of `leaf`, a key field's included, or none. -/
def CheckedParallelFieldPair.ordinaryBinding? (pair : CheckedParallelFieldPair model)
    (leaf : ValidationConditionLeaf model) : Option ParallelOrdinaryBinding :=
  let common := match pair.groups.outerScopePlan with | .common shared | .framed _ shared _ => shared
  let (first, second) : ParallelFieldSide × ParallelFieldSide :=
    if pair.errorField == pair.leftDeclaration.id then (.left, .right) else (.right, .left)
  let scopeOf : ParallelFieldSide → List RepeatableLevel
    | .left => pair.leftDeclaration.repeatableScope
    | .right => pair.rightDeclaration.repeatableScope
  match ValidationCondition.ordinaryIterationScope (.leaf leaf) with
  | .ok none => some .common
  | .ok (some scope) =>
      if scope.isPrefixOf common then some .common
      else if scope.isPrefixOf (scopeOf first) then some (.side first)
      else if scope.isPrefixOf (scopeOf second) then some (.side second)
      else none
  | .error _ => none

/-- Whether a binding fixes every iterating read of an ordinary leaf. A read below a joined group,
through starred children or a fixed subgroup, binds that side's joined row, an unmatched side's
key-only row included, whose children read empty (parallel-child capture, rows `q01`–`q09` and
`r01`–`r05`, two starred levels deep in `r04`, 2026-10-14). A rule declared inside a joined group
is admitted on the same account; the capture checks one statically (`y2`), not at runtime. A read
in a repeatable frame enclosing a joined group is unmeasured beside a join, as are
current-repetition and custom leaves. The Kernel refuses a join inside an indexed group as a whole
(`MVK_MULTIPLE_INDEX_FIELDS`, joined-carrier-limits rows `e01`–`e05`), which this gate refuses
without a class; `RepetitionNotUnique` beside a join takes its class from the reader's whole-rule
gate first (`d06`). -/
def CheckedParallelFieldPair.ordinaryAdmitted (pair : CheckedParallelFieldPair model)
    (leaf : ValidationConditionLeaf model) : Bool :=
  let joined := [pair.groups.leftGroup.path, pair.groups.rightGroup.path]
  let placed := model.fields.all fun declaration =>
    !leaf.referencesField declaration.id || joined.all fun path =>
      path.isPrefixOf declaration.groupPath ||
        !declaration.groupPath.isPrefixOf path || declaration.repeatableScope.isEmpty
  let measured := match leaf with
    | .repetitionNotUnique .. | .guardedRootCurrentRepetition ..
    | .guardedRepeatableCurrentRepetition .. | .customCondition _ | .customFieldValidity _
    | .indexedCustomFieldValidity _ => false
    | _ => true
  measured && placed && (pair.ordinaryBinding? leaf).isSome

def CheckedParallelFieldPair.admitsOperand (pair : CheckedParallelFieldPair model)
    (operand : ParallelFieldOperand) : Bool :=
  let declaration := pair.declaration operand
  let scope := match pair.groups.outerScopePlan with
    | .common common => common
    | .framed _ common frame => common ++ frame
  (model.lookupUniqueId declaration.id).toOption == some declaration &&
    ((pair.groups.leftGroup.path.isPrefixOf declaration.groupPath &&
        declaration.repeatableScope == pair.leftDeclaration.repeatableScope) ||
     (pair.groups.rightGroup.path.isPrefixOf declaration.groupPath &&
        declaration.repeatableScope == pair.rightDeclaration.repeatableScope) ||
     declaration.repeatableScope.isPrefixOf scope)

namespace ParallelNumericAtomOf

/-- The aggregate's resolved Number list, or none when any operand is not a Number field. -/
def aggregateFields? (pair : CheckedParallelFieldPair model) (operands : List ParallelFieldOperand) :
    Option ResolvedNumericAggregateFields :=
  match operands.mapM fun operand => (pair.declaration operand).toNumberField? with
  | some (first :: rest) => some { first, rest }
  | _ => none

/-- The operands' stored String or Enumeration projections, or none when any operand has none. -/
def tokenOperands? (pair : CheckedParallelFieldPair model) (operands : List ParallelFieldOperand) :
    Option (List FlatTextFieldOperand) :=
  operands.mapM fun operand => ((pair.declaration operand).toTokenFieldComparison? .stored).map (·.1)

/-- Two or more distinct String or Enumeration fields, the operand list a distinct count and a
uniqueness test take over a joined pair (joined-carrier-limits capture, rows `d01b`, `d03` and `d04`,
2026-10-14). -/
def tokenList (pair : CheckedParallelFieldPair model) (operands : List ParallelFieldOperand) : Bool :=
  (tokenOperands? pair operands).isSome && 1 < operands.length &&
    (operands.map (pair.declaration · |>.id)).Nodup

/-- A distinct count over a token list. -/
def tokenDistinct (pair : CheckedParallelFieldPair model) :
    NumericAggregateOp → List ParallelFieldOperand → Bool
  | .distinctCount, operands => tokenList pair operands
  | _, _ => false

/-- The temporal gates are the ordinary ones; the stored-component decoder is the model's own, so the atom carries none. -/
def admitted (pair : CheckedParallelFieldPair model) : ParallelNumericAtom model → Bool
  | .field operand => (pair.declaration operand).toNumberField?.isSome
  | .temporalPart operand part =>
      match (pair.declaration operand).toTemporalField? with
      | some source => model.admitsTemporalNumericPart source part (model.temporalNumericPartialFormat source.id)
      | none => false
  | .aggregate op operands => tokenDistinct pair op operands || (aggregateFields? pair operands).any fun source =>
      source.hasMultipleFields && source.hasUniqueFields
  | .ordinary leaf => leaf.orderedAtom?.isSome && pair.ordinaryAdmitted leaf

def scaleSummary (pair : CheckedParallelFieldPair model) :
    ParallelNumericAtom model → NumericScaleSummary
  | .field operand =>
      match (pair.declaration operand).toNumberField? with
      | some number => .field number.info.scale
      | none => { scale := .unknown, canExpandScale := false }
  | .temporalPart .. => .field 0
  | .aggregate op operands =>
      match aggregateFields? pair operands with
      | some source => op.scaleSummary source
      | none => if tokenDistinct pair op operands then .field 0 else { scale := .unknown, canExpandScale := false }
  | .ordinary leaf => (leaf.orderedAtom?.map (·.summary)).getD { scale := .unknown, canExpandScale := false }

/-- An absent joined observation is call-local unavailability without an invented formal cause; a present one enters the ordinary validation fold, so empty and invalid operands stay UNKNOWN or substituted rather than poisoning. -/
def resolveValidation (pair : CheckedParallelFieldPair model)
    (read : ParallelFieldOperand → Except ParallelPresenceRuleEvaluationError (Option CellObservation))
    (readOrdinary : ValidationConditionLeaf model →
      Except ParallelPresenceRuleEvaluationError (Except NumericValidationUnavailable NumericArithmeticOutcome)) :
    ParallelNumericAtom model →
      Except ParallelPresenceRuleEvaluationError (Except NumericValidationUnavailable NumericArithmeticOutcome)
  | .field operand => do
      let some number := (pair.declaration operand).toNumberField? | throw .unsupportedCondition
      pure (((← read operand).map fun cell =>
        (cell.asDirectNumericComparisonOperand number.info).toValidationArithmetic).getD
          (.error NumericValidationUnavailable.silentlyUnavailable))
  | .temporalPart operand part => do
      let some source := (pair.declaration operand).toTemporalField? | throw .unsupportedCondition
      pure (((← read operand).map fun cell =>
        (cell.asStoredTemporalNumericOperand source part
          (model.temporalNumericPartialFormat source.id)).toValidationArithmetic).getD
            (.error NumericValidationUnavailable.silentlyUnavailable))
  | .aggregate op operands => do
      let some source := aggregateFields? pair operands | do
        -- A token distinct count folds the ordinary value-list cells of the joined observations.
        let some tokens := tokenOperands? pair operands | throw .unsupportedCondition
        let observed ← operands.mapM read
        let some cells := observed.mapM id | return .error NumericValidationUnavailable.silentlyUnavailable
        let side : ResolvedValueListSide .token := {
          cells := (tokens.zip cells).map fun (token, cell) => token.observedValueListCell cell
          hasUninstantiatedTail := false, hasHaving := false }
        pure (evalDistinctCountAggregate side).toValidationArithmetic
      let observed ← operands.mapM fun operand => do
        pure ((pair.declaration operand).id, ← read operand)
      match observed.mapM fun (id, cell) => cell.map (id, ·) with
      | none => pure (.error NumericValidationUnavailable.silentlyUnavailable)
      | some cells => pure (source.evaluate op
          (fun id => (cells.lookup id).getD (.unknown .malformed))).toValidationArithmetic
  | .ordinary leaf => readOrdinary leaf

end ParallelNumericAtomOf

namespace ParallelFieldLeaf

/-- The one-atom leaves of a comparison's ordinary atoms. -/
def atomLeaves : ParallelFieldLeaf model → List (ValidationConditionLeaf model)
  | .comparison value => (value.left.atoms ++ value.right.atoms).filterMap fun
      | .ordinary leaf => some leaf
      | _ => none
  | _ => []

def fields : ParallelFieldLeaf model → List ParallelFieldOperand
  | .groupPresence _ _ => []
  | .presence field _ => [field]
  | .numeric _ lhs rhs | .fill _ lhs rhs => [lhs, rhs]
  | .comparison value => (value.left.atoms ++ value.right.atoms).flatMap (·.operands)
  | .customCondition _ => []
  | .valuesNotUnique operands => operands
  | .flat _ reads => reads
  | .ordinary _ => []

def uses (pair : CheckedParallelFieldPair model) (side : ParallelFieldSide)
    (leaf : ParallelFieldLeaf model) : Bool :=
  let group := match side with | .left => pair.groups.leftGroup | .right => pair.groups.rightGroup
  match leaf with
  | .groupPresence _ reference => group.path.isPrefixOf reference.path
  -- A side-bound ordinary leaf reads that side's joined row; a common-bound one reads neither.
  | .ordinary condition => pair.ordinaryBinding? condition == some (.side side)
  | _ => leaf.fields.any (fun field => group.path.isPrefixOf (pair.declaration field).groupPath) ||
      leaf.atomLeaves.any (pair.ordinaryBinding? · == some (.side side))

/-- Every payload is model-owned and addressable from the join or frame; comparisons reuse the shared authoring and scale gates. -/
def admitted (pair : CheckedParallelFieldPair model) (suppress : Bool)
    (leaf : ParallelFieldLeaf model) : Bool :=
  leaf.fields.all (CheckedParallelFieldPair.admitsOperand pair) && match leaf with
  | .numeric op lhs rhs =>
      match (pair.declaration lhs).toNumberField?, (pair.declaration rhs).toNumberField? with
      | some a, some b => (NumericValidationOp.ordinary op).acceptsScalesWithSuppression suppress
          (.field a.info.scale) (.field b.info.scale)
      | _, _ => false
  | .groupPresence _ reference =>
      let scope := model.repeatableScopeForGroupPath reference.path
      model.hasGroupPath reference.path && reference.boundRepeatableScope == scope &&
        ((pair.groups.leftGroup.path.isPrefixOf reference.path &&
            scope == pair.leftDeclaration.repeatableScope) ||
         (pair.groups.rightGroup.path.isPrefixOf reference.path &&
            scope == pair.rightDeclaration.repeatableScope) ||
         reference.path.isPrefixOf pair.groups.commonParent)
  | .presence _ _ => true
  | .fill _ lhs rhs => (pair.declaration lhs).id != (pair.declaration rhs).id
  | .comparison value =>
      { value with suppressExactScaleWarning := suppress }.admittedWith
        (·.admitted pair) (·.scaleSummary pair)
  | .customCondition _ => true
  | .valuesNotUnique operands => ParallelNumericAtomOf.tokenList pair operands
  | .flat condition reads => model.fields.all fun declaration =>
      !condition.referencesField declaration.id || reads.any (pair.declaration · == declaration)
  | .ordinary leaf => pair.ordinaryAdmitted leaf

/-- Direct fields and operation-list wrappers retain the ordinary literal-sensitive guard;
composite arithmetic has its own parse-tree branch (spec/07 §2). A field list is an entity list in the
ordinary guard: it rejects mixed references like a wrapper, and a distinct count keeps the ordinary
positive-threshold rule. -/
private def numericGuard (participates : ParallelFieldOperand → Bool)
    (value : NumericComparisonOf (ParallelNumericAtom model)) : IterationGuardStatus :=
  let rec sensitive : AuthoredNumericExpr (ParallelNumericAtom model) → Option Bool
    | .group body => sensitive body
    | .atom (.aggregate ..) => some true
    -- An ordinary atom reads no joined field, so it neither participates nor wraps one.
    | .atom _ => some false
    | .abs _ | .round _ _ _ | .extremum _ _ _ | .extremumCall _ _ => some true
    | _ => none
  let rec distinctCount : AuthoredNumericExpr (ParallelNumericAtom model) → Bool
    | .group body => distinctCount body
    | .atom (.aggregate .distinctCount _) => true
    | _ => false
  let atomOperands := fun (expression : AuthoredNumericExpr (ParallelNumericAtom model)) =>
    expression.atoms.flatMap (·.operands)
  let classify expression constant (entityOnLeft : Bool) := do
    let rejectMixed ← sensitive expression
    let .literal literal := constant | none
    let bits := (atomOperands expression).map participates
    if !bits.any id then return IterationGuardStatus.noReference
    if rejectMixed && !bits.all id then return .unguarded
    let some converted := literal.javaRoundedInt32? | return .unclassified
    -- The ordinary carrier's positive-threshold rule: `> 1` guards, `< 2` does not
    -- (joined-carrier-limits capture, rows `d01b` and `d02b`, 2026-10-14).
    if distinctCount expression then
      return if 0 < converted && ValidationCondition.positiveCountThresholdIsUnguarded entityOnLeft value.op then .unguarded
        else .guarded
    pure (value.op.literalIterationGuard converted bits rejectMixed)
  match classify value.left value.right true with
  | some result => result
  | none => match classify value.right value.left false with
    | some result => result
    | none =>
        if (atomOperands value.left ++ atomOperands value.right).any participates then .guarded
        else .noReference

/-- Presence quantifiers share one participation rule for ordinary and parallel iteration.
The two mixed-sensitive operators require every operand to iterate (spec/07 §2; IterationNotValidVisitor). -/
private def fillGuard (participates : ParallelFieldOperand → Bool)
    (op : FieldFillQuantifier) (left right : ParallelFieldOperand) : IterationGuardStatus :=
  if !(participates left || participates right) then .noReference else
    match op with
    | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled => .unguarded
    | .atLeastOneFieldFilled | .fieldsNotCollectivelyFilled =>
        if participates left && participates right then .guarded else .unguarded
    | .allFieldsFilled | .moreThanOneFieldFilled => .guarded

/-- For direct fields on the joined pair, the parallel guard follows the source operator's iteration test, not its runtime empty verdict (Kernel `IterationNotValidVisitor`). -/
def guards (pair : CheckedParallelFieldPair model) : ParallelFieldLeaf model → Bool
  | leaf@(.groupPresence .filled _) => leaf.uses pair .left || leaf.uses pair .right
  | .groupPresence .notFilled _ => false
  | leaf@(.presence _ .filled) | leaf@(.numeric _ _ _) =>
      leaf.uses pair .left || leaf.uses pair .right
  | .comparison value => decide (numericGuard (fun field =>
      pair.groups.leftGroup.path.isPrefixOf (pair.declaration field).groupPath ||
      pair.groups.rightGroup.path.isPrefixOf (pair.declaration field).groupPath) value = .guarded)
  | .presence _ .notFilled => false
  | .fill op left right => decide (fillGuard (fun field =>
      pair.groups.leftGroup.path.isPrefixOf (pair.declaration field).groupPath ||
      pair.groups.rightGroup.path.isPrefixOf (pair.declaration field).groupPath) op left right = .guarded)
  | .customCondition _ | .ordinary _ | .valuesNotUnique _ => false
  | .flat condition reads => decide (condition.iterationGuard (fun field =>
      reads.any fun operand => (pair.declaration operand).id == field &&
        (pair.groups.leftGroup.path.isPrefixOf (pair.declaration operand).groupPath ||
          pair.groups.rightGroup.path.isPrefixOf (pair.declaration operand).groupPath)) = .guarded)

/-- A one-sided frame has ordinary iteration levels in addition to the parallel key level. Direct pair leaves specialize the existing iteration guard table at each such level. -/
def guardAt (pair : CheckedParallelFieldPair model) (level : RepeatableLevel)
    (value : ParallelFieldLeaf model) : IterationGuardStatus :=
  match value with
  | .comparison value => numericGuard (fun field => (pair.declaration field).repeatableScope.contains level) value
  | .groupPresence op reference =>
      if !reference.boundRepeatableScope.contains level then .noReference
      else if op.canFireOnEmpty then .unguarded else .guarded
  | .fill op left right => fillGuard
      (fun field => (pair.declaration field).repeatableScope.contains level) op left right
  | .presence field op =>
      if !(pair.declaration field).repeatableScope.contains level then .noReference
      else match op with | .filled => .guarded | .notFilled => .unguarded
  | .numeric _ left right =>
      if (pair.declaration left).repeatableScope.contains level ||
          (pair.declaration right).repeatableScope.contains level then .guarded else .noReference
  | .customCondition _ | .ordinary _ => .noReference
  | .valuesNotUnique operands =>
      if operands.any (fun operand => (pair.declaration operand).repeatableScope.contains level) then .unclassified
      else .noReference
  | .flat condition reads => condition.iterationGuard fun field =>
      reads.any fun operand => (pair.declaration operand).id == field &&
        (pair.declaration operand).repeatableScope.contains level

/-- Joined group reads preserve index unavailability before deriving physical group content; ancestors use the same outer coordinates without acquiring a join-level reference. -/
private def groupState (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) (reference : ResolvedGroupReference) :
    Except ParallelPresenceRuleEvaluationError GroupPresenceState := do
  let side := if row.left.group.path.isPrefixOf reference.path then some row.left
    else if row.right.group.path.isPrefixOf reference.path then some row.right else none
  let environment := match side with
    | some selected => selected.environment
    | none => row.left.environment.orElse fun _ => row.right.environment
  match environment with
  | some environment =>
      let input ← preliminary.groupPresenceInput reference.path environment .fullyRelevant false
        |>.mapError .group
      pure input.derive
  | none =>
      pure {
        content := false
        erroneous := false
        relevance := if side.any (·.unavailableKey.isSome) then .noneRelevant else .fullyRelevant }

/-- The checked cell whose validation observation is exactly `observation`, for a flat leaf that
reads cells. An empty observation has no placement, since a joined read cannot tell absent from
present-empty and the flat consumers treat both alike. -/
private def _root_.A12Kernel.CellObservation.asCheckedCell : CellObservation → CheckedCell
  | .empty => { rawPresent := false, parsed := none, findings := [] }
  | .value value => { rawPresent := true, parsed := some value, findings := [] }
  | .unknown cause | .poison cause => { rawPresent := true, parsed := none, findings := [cause] }

/-- Full and partial calls share scalar consumers; absent observations mean call-local unavailability without an invented formal cause. The callback is consulted only for a custom leaf the fold reaches, and its truth is VALUE-typed; the default resolves nothing, so a reached name reports a missing registration. -/
def evalWith (pair : CheckedParallelFieldPair model)
    (read : ParallelFieldOperand → Except ParallelPresenceRuleEvaluationError (Option CellObservation))
    (readGroup : ResolvedGroupReference → Except ParallelPresenceRuleEvaluationError GroupPresenceState)
    (readOrdinary : ValidationConditionLeaf model → Except ParallelPresenceRuleEvaluationError Verdict)
    (readAtom : ValidationConditionLeaf model →
      Except ParallelPresenceRuleEvaluationError (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (leaf : ParallelFieldLeaf model)
    (custom : String → Except CustomConditionLookupError Bool := fun name => .error (.missingRegistration name))
    (world : Option World := none) :
    Except ParallelPresenceRuleEvaluationError Verdict :=
  match leaf with
  | .groupPresence op reference => do
      pure (op.eval (← readGroup reference))
  | .presence side op => do
      pure ((← read side).map op.eval |>.getD .unknown)
  | .numeric op lhs rhs => do
      let some a := (pair.declaration lhs).toNumberField? | throw .unsupportedCondition
      let some b := (pair.declaration rhs).toNumberField? | throw .unsupportedCondition
      let leftValue ← read lhs
      let rightValue ← read rhs
      match leftValue, rightValue with
      | some left, some right =>
          pure (op.eval (left.asDirectNumericComparisonOperand a.info)
            (right.asDirectNumericComparisonOperand b.info))
      | _, _ => pure .unknown
  | .comparison value => do
      let left ← value.left.mapM (·.resolveValidation pair read readAtom)
      let right ← value.right.mapM (·.resolveValidation pair read readAtom)
      pure ({ value with left, right }.evalWith id)
  | .fill op lhs rhs => do
      let unknown : ValidationFillTally := { filled := 0, empty := 0, unknown := 1, uninstantiated := 0 }
      let left ← read lhs
      let right ← read rhs
      pure ((op.evalValidation ((left.map (·.asValidationFillTally) |>.getD unknown).combine
        (right.map (·.asValidationFillTally) |>.getD unknown))).asConservativeVerdict)
  | .customCondition name => do
      pure (customConditionVerdict (← (custom name.value).mapError .customCondition))
  | .valuesNotUnique operands => do
      let some tokens := ParallelNumericAtomOf.tokenOperands? pair operands | throw .unsupportedCondition
      let some cells := (← operands.mapM read).mapM id | return .unknown
      pure (evalValuesNotUniqueVerdict ((tokens.zip cells).map fun (token, cell) =>
        (token.observedValueListCell cell, false)))
  | .flat condition reads => do
      -- Each read is one joined observation, so the leaf's ordinary semantics see an unmatched
      -- partner as empty, the same observation a presence leaf sees (parallel-flat-leaves capture, 2026-10-14).
      let observed ← reads.mapM fun operand => do pure ((pair.declaration operand).id, ← read operand)
      if observed.any (·.2.isNone) then return .unknown
      let context : FlatContext := {
        read := fun field => match observed.find? (·.1 == field) with
          | some (_, some observation) => observation.asCheckedCell
          | _ => malformedCheckedCell
        world }
      pure (condition.evalSelected context)
  | .ordinary leaf => readOrdinary leaf

/-- The environment an ordinary leaf reads at one joined row: the common outer one, or its bound
side's row, a key-only row for an unmatched side. The flag marks that key-only row. -/
def ordinaryEnvironment? (pair : CheckedParallelFieldPair model) (document : CheckedDocument model)
    (row : ResolvedParallelIndexRow) (outer : Env) (leaf : ValidationConditionLeaf model) :
    Option (Env × Bool) :=
  match pair.ordinaryBinding? leaf with
  | some .common | none => some (outer, false)
  | some (.side side) =>
      let joined := match side with | .left => row.left | .right => row.right
      match joined.environment with
      | some environment => some (environment, false)
      | none => (document.keyOnlyEnvironment? outer joined.group).map (·, true)

/-- Evaluate one ordinary leaf in a partial view. A reached temporal fault has no parallel
runtime-failure route; it fails the call, as in full validation. -/
def evalPartialOrdinary (view : CheckedPartialPreliminary model) (environment : Env)
    (world : Option World) (leaf : ValidationConditionLeaf model) :
    Except ParallelPresenceRuleEvaluationError Verdict :=
  match ValidationCondition.evalPartialAddressedResult (.leaf leaf) view
      (view.addressedValidationContext environment world) environment none with
  | .ok verdict => pure verdict
  | .error (.inl (.conditionAddressing error)) => throw (.addressing error)
  | .error (.inl _) => throw .unsupportedCondition
  | .error (.inr _) => throw (.addressing .temporalUnavailable)

/-- Missing and invalid joined sides enter the same scalar observation consumers as physical reads. -/
def eval (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) (outer : Env)
    (custom : String → Except CustomConditionLookupError Bool) (world : Option World := none) : ParallelFieldLeaf model →
    Except ParallelPresenceRuleEvaluationError Verdict :=
  fun leaf => evalWith pair
    (fun field => do
      let declaration := pair.declaration field
      if row.left.group.path.isPrefixOf declaration.groupPath ||
          row.right.group.path.isPrefixOf declaration.groupPath then
        (row.readValidation preliminary declaration.id).map some |>.mapError .join
      else
        let path ← outer.pathForScope declaration.repeatableScope
          |>.mapError (fun error => .join (.environment error))
        let cell ← preliminary.readAuthoredValidation { field := declaration.id, path }
          |>.mapError (fun error => .join (.document error))
        pure (some (observeCell .validation cell)))
    (groupState row preliminary)
    -- The full evaluator reads only instantiated rows; a key-only row is read through the
    -- full-relevance partial view, which reads an absent declared slot as empty.
    (fun leaf => match ordinaryEnvironment? pair preliminary.base row outer leaf with
      | none => pure .unknown
      | some (environment, true) => do
          let view ← preliminary.base.applyPartialGeneratedPreliminaryForScope .full |>.mapError .preliminary
          evalPartialOrdinary view environment world leaf
      | some (environment, false) => ValidationCondition.evalAddressed (.leaf leaf) (addressedAt environment)
        |>.mapError .addressing)
    -- An ordinary comparison atom resolves at its leaf's binding, as that leaf would evaluate.
    (fun carrier => do
      let some atom := carrier.orderedAtom? | throw .unsupportedCondition
      match ordinaryEnvironment? pair preliminary.base row outer carrier with
      | none => pure (.error .silentlyUnavailable)
      | some (environment, true) => do
          let view ← preliminary.base.applyPartialGeneratedPreliminaryForScope .full |>.mapError .preliminary
          (atom.resolveAddressed (view.addressedValidationContext environment world)).mapError .addressing
      | some (environment, false) => (atom.resolveAddressed (addressedAt environment)).mapError .addressing)
    leaf custom world
where
  addressedAt (environment : Env) : AddressedValidationEvaluationContext model := {
    scalar := { fields := { preliminary.base.flatContext with world }, groups := GroupPresenceContext.unavailable }
    outer := environment, input := .checked preliminary.base }

end ParallelFieldLeaf

namespace ParallelFieldCondition

/-- A conjunction needs a guarding member; every disjunction branch needs one (`IterationNotValidVisitor.visit(ICompositeCondition)`). -/
def guarded (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition model) : Bool :=
  condition.iterationGuarded (ParallelFieldLeaf.guards pair)

/-- Common outer coordinates are caller-bound; each extra frame level needs a guard from its own side. -/
def framesGuarded (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition model) : Bool :=
  match pair.groups.outerScopePlan with
  | .common _ => true
  | .framed _ common frame => frame.all fun level =>
      common.contains level || decide
        (condition.iterationGuardStatus (ParallelFieldLeaf.guardAt pair level) = .guarded)

def admitted (pair : CheckedParallelFieldPair model) (suppress : Bool)
    (condition : ParallelFieldCondition model) : Bool :=
  condition.allLeaves (ParallelFieldLeaf.admitted pair suppress) &&
    condition.anyLeaf (ParallelFieldLeaf.uses pair .left) &&
    condition.anyLeaf (ParallelFieldLeaf.uses pair .right) && condition.guarded pair && framesGuarded pair condition

/-- Authored references alone satisfy the error-target gate; topology anchor declarations are not implicit condition references. -/
def references (pair : CheckedParallelFieldPair model) : ParallelFieldCondition model → List ConditionReference
  | .leaf (.groupPresence _ reference) => [{
      isGroup := true, isRootGroup := reference.path.length == 1,
      ancestorOrEqual := reference.path.isPrefixOf
        (if pair.errorField == pair.leftDeclaration.id then pair.leftDeclaration.groupPath
         else pair.rightDeclaration.groupPath) }]
  | .leaf (.ordinary leaf) => ordinaryReferences leaf
  | .leaf leaf => leaf.fields.map (fun field =>
      { sameEntity := (pair.declaration field).id == pair.errorField }) ++ leaf.atomLeaves.flatMap ordinaryReferences
  | .and left right | .or left right => references pair left ++ references pair right
where
  ordinaryReferences (leaf : ValidationConditionLeaf model) : List ConditionReference :=
    (model.fields.filter (leaf.referencesField ·.id)).map fun declaration =>
      { sameEntity := declaration.id == pair.errorField }

def errorTargetRefusal (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition model) :
    Option KernelStaticDiagnostic :=
  conditionSideRefusal {
    declaration := .declared true, references := condition.references pair,
    iteration := {
      parallelIteration := true
      indexFieldLevel := (if pair.errorField == pair.leftDeclaration.id then pair.groups.leftGroup.path
        else pair.groups.rightGroup.path).length - 1 } }

end ParallelFieldCondition

structure CheckedParallelFieldRule (model : FlatModel) where
  private mk ::
  pair : CheckedParallelFieldPair model
  condition : ParallelFieldCondition model
  suppressExactScaleWarning : Bool
  errorTargetAllowed : condition.errorTargetRefusal pair = none
  admitted : condition.admitted pair suppressExactScaleWarning = true

/-- Public construction retains the pair's topology certificate and checks the entire condition before any read. -/
def checkParallelFieldRule (model : FlatModel)
    (leftField rightField errorField : FieldId) (condition : ParallelFieldCondition model)
    (errorCode : String) (severity : ValidationSeverity) (messagePlan : MessageRenderPlan)
    (suppressExactScaleWarning : Bool := false) :
    Except ParallelPresenceRuleAssemblyError (CheckedParallelFieldRule model) := do
  let pair ← checkParallelFieldPair model leftField rightField errorField errorCode severity messagePlan
  if hTarget : condition.errorTargetRefusal pair = none then
    if h : condition.admitted pair suppressExactScaleWarning = true then
      pure { pair, condition, suppressExactScaleWarning, errorTargetAllowed := hTarget, admitted := h }
    -- A tree whose leaves are admitted and reach both sides but whose iteration is unguarded draws the
    -- Kernel's parallel-iteration class (`FieldNotFilled(L) And FieldNotFilled(M)`, a pair `Or` a custom
    -- leaf; `IterationNotValidVisitor`). Other incoherence keeps no class.
    else if condition.allLeaves (ParallelFieldLeaf.admitted pair suppressExactScaleWarning) &&
        condition.anyLeaf (ParallelFieldLeaf.uses pair .left) &&
        condition.anyLeaf (ParallelFieldLeaf.uses pair .right) && !condition.guarded pair then
      throw (.static .parallelIterationInvalid)
    else throw .incoherentCondition
  else
    match condition.errorTargetRefusal pair with
    | some diagnostic => throw (.static diagnostic)
    | none => throw .incoherentCondition

/-- The custom-condition callbacks of one joined row. Registry lookup runs when a reached leaf calls them, so an unregistered name is observable only on a row whose fold gets that far. -/
def CheckedParallelFieldPair.customConditions (pair : CheckedParallelFieldPair model)
    (registry : CustomValidationRegistry model) (document : CheckedDocument model)
    (relevance : CustomConditionRelevance ValidationRelevanceScope) (generatedFormalFailures : List CellAddr)
    (row : ResolvedParallelIndexRow) (outer : Env) : String → Except CustomConditionLookupError Bool :=
  fun name => registry.evaluate name
    (CustomValidationInvocation.ofDocument document relevance (pair.customErrorPointer row outer)
      generatedFormalFailures)

/-- Whether a leaf enables the classification pass, as its ordinary counterpart does
(`ValidationConditionLeaf.requiresClassificationPass`). Of these, only the fill quantifier is measured
on this carrier: `P01` of the custom-condition call capture calls its callback twice. -/
def ParallelFieldLeaf.requiresClassificationPass : ParallelFieldLeaf model → Bool
  | .groupPresence op reference => !reference.isRoot || op == .notFilled
  | .presence _ op => op == .notFilled
  | .numeric .. | .comparison _ => true
  | .fill op _ _ => match op with
    | .allFieldsFilled | .moreThanOneFieldFilled => false
    | _ => true
  | .customCondition _ | .valuesNotUnique _ => false
  | .flat condition _ => (ValidationConditionLeaf.flat (model := model) condition).requiresClassificationPass
  | .ordinary leaf => leaf.requiresClassificationPass

/-- A tree holding a custom leaf reaches it as the generated rule does: a Boolean pass that ends an
`And` at a non-firing operand, then the classification pass only when the tree holds and enables it
(`ConditionTree.evalObservedM`). `P01`'s callback is called only at the joined row where its fill
quantifier fires, and `M04` stays silent where every key has both sides filled (rows `f-full` and
`r1-rows23` of the custom-condition call capture). Other trees keep the verdict fold and its UNKNOWN. -/
def ParallelFieldCondition.evalReached (condition : ParallelFieldCondition model)
    (evalLeaf : ParallelFieldLeaf model → Except ParallelPresenceRuleEvaluationError Verdict) :
    Except ParallelPresenceRuleEvaluationError Verdict :=
  if condition.anyLeaf (fun | .customCondition _ => true | _ => false) then
    condition.evalObservedM (condition.anyLeaf ParallelFieldLeaf.requiresClassificationPass) evalLeaf
  else condition.evalVerdictExcept evalLeaf

/-- The failure the rule's whole-rule handler catches: a reached custom condition no factory registers (spec/11 §14). -/
def ParallelPresenceRuleEvaluationError.caughtByRule : ParallelPresenceRuleEvaluationError → Bool
  | .customCondition (.missingRegistration _) => true
  | _ => false

/-- Run each outer row in order, ending after the first whose traversal a caught failure stopped.
A failure in a later outer row reports at that row's first joined row; the capture measures a single
outer row only. -/
def ParallelRuleRowOutcome.untilCaught
    (run : Env → Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome)) :
    List Env → Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome)
  | [] => pure []
  | outer :: remaining => do
      let outcomes ← run outer
      if outcomes.any (·.outcome.message?.any (·.origin == .runtimeFailure)) then pure outcomes
      else pure (outcomes ++ (← untilCaught run remaining))

/-- Execute the certified tree on the shared lexical join/frame traversal. Structural failures stay separate from semantic UNKNOWN. Full validation hands a custom callback the all-relevant marker and the base document's own findings. -/
def CheckedParallelFieldRule.evalFull (rule : CheckedParallelFieldRule model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := [])
    (messageCache : Option MessageIndexContext := none)
    (registry : CustomValidationRegistry model := {}) (world : Option World := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) :=
  rule.pair.evalWith rule.condition
    (fun outer row view => rule.condition.evalReached
      (ParallelFieldLeaf.eval rule.pair row view outer
        (rule.pair.customConditions registry view.base .all [] row outer) world))
    preliminary outer messageCache (caught := ParallelPresenceRuleEvaluationError.caughtByRule)

/-- Parallel unions are local to each in-capacity common outer row. An implicit outer row has no child index entries, hence no parallel evaluation to fabricate. -/
def CheckedParallelFieldRule.evalDocument (rule : CheckedParallelFieldRule model)
    (preliminary : CheckedIndexPreliminary model)
    (messageCache : Option MessageIndexContext := none)
    (registry : CustomValidationRegistry model := {}) (world : Option World := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) := do
  let scope := match rule.pair.groups.outerScopePlan with
    | .common shared | .framed _ shared _ => shared
  let environments ← if scope.isEmpty then pure [[]]
    else preliminary.base.inCapacityRowEnvironments scope |>.mapError .rows
  ParallelRuleRowOutcome.untilCaught (fun outer => rule.evalFull preliminary outer messageCache registry world)
    environments

end A12Kernel
