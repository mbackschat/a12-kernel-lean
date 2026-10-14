import A12Kernel.Reference.Dm.LowerString
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Reference.Dm.LowerRows
import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.MixedComputationPlan
import A12Kernel.Elaboration.ComputationNumericGuard

/-! # Running a DM model's computations over one document

Each computation is parsed and lowered onto the checked table of its target's kind, which joins its
common precondition onto every alternative, or refused by the construct no carrier admits. The lowered
steps, Number and String tables, whole-document targets and repeatable row operations, are certified
together as one `MixedComputationPlan` and executed in its order over the checked document.

The result is projected onto what a Kernel `compute` observation reports: its change projection,
an instance whose computed value equals its stored value being no change, a target that held a
value and now holds none being cleared, and a rejected attempt being errored. A Number step supplies
that projection itself (`NumericComputationRunView`); for String and whole-document targets it is
taken against the stored text.
-/

namespace A12Kernel.Dm

/-- One reported computation outcome: `value <text>`, `cleared` or `errored <text>`. -/
structure ComputedOutcome where
  pointer : String
  outcome : String
  deriving Repr, BEq, Ord, Inhabited

instance : ToString ComputedOutcome where
  toString computed := s!"{computed.pointer}={computed.outcome}"

private def scalarMembershipOp? : String → Option ValueListMembershipOp
  | "FieldValueIncludedInValueList" => some .included
  | "FieldValueNotIncludedInValueList" => some .notIncluded
  | _ => none

private def scalarMembershipSubject? : Expr → Option SurfaceTextFieldOperand
  | .entity { path, index := none, category, filter := none } => do
      let field ← path.toFieldPath?
      pure (match category with | none => .direct field | some name => .category field name)
  | _ => none

private def lowerScalarMembership (operator : ValueListMembershipOp)
    (arguments : List Argument) : Lowering SurfaceComputationPredicate := do
  let .mk subject none :: members := arguments | refuse "Guard/Membership" "subject"
  let some subject := scalarMembershipSubject? subject | refuse "Guard/Membership" "bare subject"
  let some members := members.mapM (fun | .mk expr none => some expr | _ => none)
    | refuse "Guard/Membership" "members"
  let numbers := members.mapM fun
    | .number text => (decodeNumber? text).bind fun literal =>
        if literal.authoredScale == 0 then some literal.value.num else none
    | _ => none
  let tokens := members.mapM fun | .string text => some text | _ => none
  match numbers, tokens with
  | some values, _ => pure (.scalarMembership operator subject (.numbers values))
  | _, some values => pure (.scalarMembership operator subject (.tokens values))
  | _, _ =>
      let some fields := members.mapM Expr.textFieldValue? | refuse "Guard/Membership" "bracketed members"
      pure (.scalarMembership operator subject (.fields fields))

private def lowerPatternGuard (model : FlatModel) (group : GroupPath)
    (op : StringPatternOp) (left right : Expr) :
    Lowering (SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) := do
  let .value { path, index, category := none, filter := none } := left | refuse "Guard/Pattern" "field value"
  let some source := right.patternConstant? | refuse "Guard/Pattern" "constant source"
  match index with
  | some key => do
      let field ← lowerIndexedSource model group path key
      pure (.predicate (.indexedPattern { op, field, source }))
  | none =>
      let some field := path.toFieldPath? | refuse "Guard/Pattern" "field path"
      pure (.predicate (.pattern { op, field, source }))

/-- Lower typed guards into the shared computation condition tree. Unsupported atoms remain explicit refusals during model resolution. -/
partial def lowerGuard (model : FlatModel) (group : GroupPath) (suppress : Bool := false)
    (expression : Expr) (targetGroup? : Option GroupPath := none) :
    Lowering (SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) :=
  let filterBinding? := if expression.hasHaving then some (targetGroup?.getD group) else none
  match expression with
  | .custom _ _ => refuse "CustomCondition" CalculationRefusal.invalidLanguageFeature.catalogKey
  | .call "RepetitionNotUnique" _ none _ =>
      refuse "RepetitionNotUnique" CalculationRefusal.invalidLanguageFeature.catalogKey
  | .compare .patternMatched left right => lowerPatternGuard model group .matched left right
  | .compare .patternViolated left right => lowerPatternGuard model group .violated left right
  | .parens body => lowerGuard model group suppress body targetGroup?
  | .logic op (first :: rest) => do
      let join := match op with
        | .and => SurfaceComputationConditionOf.and
        | .or => SurfaceComputationConditionOf.or
      let mut result ← lowerGuard model group suppress first targetGroup?
      for part in rest do result := join result (← lowerGuard model group suppress part targetGroup?)
      pure result
  | .call "FieldFilled" [.mk (.entity { path, index := some key, category := none, filter := none }) none] none none =>
      (.predicate ∘ .indexedFieldPresence .filled) <$> lowerIndexedSource model group path key
  | .call "FieldNotFilled" [.mk (.entity { path, index := some key, category := none, filter := none }) none] none none =>
      (.predicate ∘ .indexedFieldPresence .notFilled) <$> lowerIndexedSource model group path key
  | .call "FieldFilled" [.mk field none] none none => match field.fieldEntity? with
      | some path => pure (.fieldFilled path)
      | none => refuse "Guard" "FieldFilled operand"
  | .call "FieldNotFilled" [.mk field none] none none => match field.fieldEntity? with
      | some path => pure (.fieldNotFilled path)
      | none => refuse "Guard" "FieldNotFilled operand"
  | .call "GroupFilled" [argument@(.mk (.entity { index := some _, filter := none, .. }) none)] none none => do
      let .keyed source .stored ← lowerEntityOperand model group argument | refuse "Guard/GroupFilled" "group operand"
      pure (.predicate (.keyedGroupPresence .filled source))
  | .call "GroupNotFilled" [argument@(.mk (.entity { index := some _, filter := none, .. }) none)] none none => do
      let .keyed source .stored ← lowerEntityOperand model group argument | refuse "Guard/GroupNotFilled" "group operand"
      pure (.predicate (.keyedGroupPresence .notFilled source))
  | .call "GroupFilled" [.mk group none] none none => match group.groupReference? with
      | some reference => pure (.groupPresence .filled reference)
      | none => refuse "Guard/GroupFilled" "group operand"
  | .call "GroupNotFilled" [.mk group none] none none => match group.groupReference? with
      | some reference => pure (.groupPresence .notFilled reference)
      | none => refuse "Guard/GroupNotFilled" "group operand"
  | .call "Valid" [.mk (.call "Date" arguments none none) none] none none =>
      (.predicate ∘ .dateValidity .valid) <$> lowerScalarDateComponents model group arguments suppress
  | .call "Invalid" [.mk (.call "Date" arguments none none) none] none none =>
      (.predicate ∘ .dateValidity .invalid) <$> lowerScalarDateComponents model group arguments suppress
  | .call "Valid" [.mk (.entity { path, index := some key, category := none, filter := none }) none, .mk (.string name) none] none none => do
      pure (.predicate (.indexedTypeValidity .valid (← lowerIndexedSource model group path key) name))
  | .call "Invalid" [.mk (.entity { path, index := some key, category := none, filter := none }) none, .mk (.string name) none] none none => do
      pure (.predicate (.indexedTypeValidity .invalid (← lowerIndexedSource model group path key) name))
  | .call "Valid" [.mk field none, .mk (.string name) none] none none => do
      let some path := field.fieldEntity? | refuse "ValidType" "field operand"
      pure (.predicate (.typeValidity .valid path name))
  | .call "Invalid" [.mk field none, .mk (.string name) none] none none => do
      let some path := field.fieldEntity? | refuse "InvalidType" "field operand"
      pure (.predicate (.typeValidity .invalid path name))
  | .call "FieldValuesNotUnique" arguments none none =>
      (.predicate ∘ .uniqueness) <$> lowerEntitySource model group arguments filterBinding? suppress
  | .call "DateRangesOverlap" arguments none none =>
      (.predicate ∘ .overlap) <$> lowerEntitySource model group arguments filterBinding? suppress
  | .call "AtLeastOneDateRangeOverlaps" [scalar] (some values) none => do
      pure (.predicate (.scalarOverlap {
        scalar := ← lowerEntityOperand model group scalar (suppress := suppress)
        list := ← lowerEntitySource model group values filterBinding? suppress }))
  | .call id arguments (some values) none => do
      let some quantifier := valueListQuantifier? id | refuse ("Guard/" ++ id)
      let fields ← lowerEntitySource model group arguments filterBinding? suppress
      match values.mapM (fun | .mk (.string value) none => some value | _ => none) with
      | some literals => pure (.predicate (.tokenLiteralValueList { quantifier, fields, values := literals }))
      | none => pure (.predicate (.entityValueList {
          quantifier, fields, values := ← lowerEntitySource model group values filterBinding? suppress }))
  | .call id arguments none none => match scalarMembershipOp? id with
      | some operator => .predicate <$> lowerScalarMembership operator arguments
      | none => match fieldFillOp? id with
          | some operator => .fieldFill operator <$> lowerEntitySource model group arguments filterBinding? suppress
          | none => match groupQuantifier? id with
              | some operator => .groupFill operator <$> lowerEntitySource model group arguments filterBinding? suppress
              | none => refuse ("Guard/" ++ id)
  | expression@(.compare op left right) => do
      if let some lowered := lowerDateRangeComparison? model group op left right then
        let (operator, source) ← lowered
        return .predicate (.dateRangeComparison operator source)
      let scalarPair : Option (SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) := do
        let left ← left.fieldValue?
        let right ← right.fieldValue?
        let declaration ← (model.resolveFieldDeclarationUnchecked group left).toOption
        let op ← op.toSurface?
        match declaration.policy.kind with
        | .boolean | .confirm | .dateRange => some (SurfaceComputationConditionOf.predicate
            (.fieldComparison op left right))
        | _ => none
      let textPair := do
        let left ← Expr.textFieldValue? left
        let right ← Expr.textFieldValue? right
        let op ← op.toSurface?
        let declaration ← (model.resolveFieldDeclarationUnchecked group left.reference).toOption
        if declaration.toTextFieldComparison?.isSome || left.projectionRef != EnumerationProjectionRef.stored then
          some (SurfaceComputationConditionOf.text op left (.inl right))
        else none
      let textSurface := (scalarPair.orElse (fun _ => textPair)).orElse fun _ => (lowerFlat model group expression).bind fun
        | .compare op field (.string expected) => some (.text op (.direct field) (.inr expected))
        | .compare op field (.boolean expected) => some (.boolean op field expected)
        | .compareEnumeration op field projection expected =>
            let source := match projection with
              | .stored => SurfaceTextFieldOperand.direct field
              | .category name => .category field name
            some (.text op source (.inr expected))
        | .compareTextFields op left right => some (.text op left (.inl right))
        | .compareFields op left right =>
            if ((model.resolveFieldDeclarationUnchecked group left).toOption.bind
                FlatFieldDecl.toTextFieldComparison?).isSome then
              some (.text op (.direct left) (.inl (.direct right)))
            else none
        | _ => none
      let stringSurface : Option (SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) := do
        let operator ← match op with | .eq => some EqualityOp.equal | .ne => some EqualityOp.notEqual | _ => none
        let left ← (lowerSelectedStringExpr model group left).toOption
        let right ← (lowerSelectedStringExpr model group right).toOption
        if isStringExpressionComparisonOperand left || isStringExpressionComparisonOperand right then
          some (SurfaceComputationConditionOf.predicate (.selectedStringExpression operator left right))
        else none
      let tokenSurface := do
        let selected : Expr → Bool
          | .call "FirstFilledValue" _ none none => true
          | .value { index := some _, category := none, .. } => true
          | _ => false
        if !selected left && !selected right then none else do
          let operator ← match op with | .eq => some EqualityOp.equal | .ne => some .notEqual | _ => none
          let left ← (lowerTokenComparisonOperand model group filterBinding? left suppress).toOption
          let right ← (lowerTokenComparisonOperand model group filterBinding? right suppress).toOption
          let _ ← (elaborateTokenComparison model group operator left right (targetGroup?.getD group)).toOption
          some (SurfaceComputationConditionOf.predicate (.tokenComparison operator left right))
      let selectedSurface := do
        let operator ← match op with | .eq => some EqualityOp.equal | .ne => some .notEqual | _ => none
        let left ← (lowerFirstFilledComparisonOperand model group filterBinding? left suppress).toOption
        let right ← (lowerFirstFilledComparisonOperand model group filterBinding? right suppress).toOption
        let _ ← (elaborateFirstFilledComparison model group (targetGroup?.getD group)
          (if operator == .equal then .equal else .notEqual) left right).toOption
        some (SurfaceComputationConditionOf.predicate (.selectedComparison operator left right))
      let temporalSurface := do
        let operator ← op.toSurface?
        let left ← (lowerScalarTemporalExpression model group left suppress).toOption
        let right ← (lowerScalarTemporalExpression model group right suppress).toOption
        match elaborateScalarTemporalComparison model group operator.toTemporal left right targetGroup? with
        | .error (.nonTemporal _) | .error (.extremum (.firstNotTemporal _ _)) => none
        | _ => some (SurfaceComputationConditionOf.predicate
            (SurfaceComputationPredicate.temporal operator.toTemporal left right))
      match (((textSurface.orElse (fun _ => stringSurface)).orElse (fun _ => tokenSurface)).orElse
          (fun _ => selectedSurface)).orElse (fun _ => temporalSurface) with
      | some surface => pure surface
      | none => do
          let some operator := op.toNumeric? | refuse "Comparison" "operator"
          let atom := fun expression => lowerCompleteComputationNumericAtom model group expression filterBinding? suppress
          pure (.numeric {
            op := operator
            left := ← lowerNumericExpr atom (lowerNumericFieldAtom model group atom) left
            right := ← lowerNumericExpr atom (lowerNumericFieldAtom model group atom) right
            suppressExactScaleWarning := suppress })
  | other => refuse ("Guard/" ++ other.construct)


private def parsed (language : Language) (text : String) : Lowering Text :=
  match parseText language text with
  | .ok text => pure text
  | .error error => refuse "Syntax" error.errorClass.code

/-- The declaration a computation targets. Its path is relative to the computation element. -/
def targetOf (language : Language) (model : FlatModel) (computation : DmComputation) :
    Lowering FlatFieldDecl := do
  let path ← match parseModelPath language computation.targetRelPath with
    | .ok path => pure path
    | .error error => refuse "Target" error.errorClass.code
  -- The path is written from the element, one step below its group; a relative path without that
  -- step is outside every retained model, so it is refused rather than read at the group.
  if !path.absolute && path.ups == 0 then refuse "Target" computation.targetRelPath
  let relative := if path.absolute then path else { path with ups := path.ups - 1 }
  let some field := relative.toFieldPath? | refuse "Target" computation.targetRelPath
  elaborated "Target" (model.resolveFieldDeclarationUnchecked computation.group field)

/-- A refused computation leaves its whole target's alternative table incomplete, even when
another computation for that target lowers. Resolve identity rather than comparing final names;
the split-target rows in `src-group-conditional-profiles` expose both false matches and divergence. -/
def hasRefusedComputationTarget (language : Language) (model : FlatModel)
    (refused : List DmComputation) (target : FieldId) : Bool :=
  refused.any fun computation =>
    (targetOf language model computation).toOption.any (·.id == target)

/-- Keep the ordinary refusal unless the joined route reached its guard's target ban: the ordinary
reader cannot bind the joined operand, so only the joined route sees that reference. -/
private def Refusal.orGuardBan (ordinary joined : Refusal) : Refusal :=
  if joined.construct == "ParallelGuard" then joined else ordinary

/-- Parse, syntax-check and lower one guard text against `model`. -/
private def guardSurface (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) (suppress : Bool) (text : String) :
    Lowering (SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) := do
  let guard := (← parsed language text).body
  if !guard.parensLegal true then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
  lowerGuard model computation.group suppress guard (some target.groupPath)

private def guardRefusal (error : CheckedComputationConditionElabError) : Refusal := {
  construct := "Guard"
  detail := (match error with
    | .predicate (.overlap cause) => cause.diagnostic?
    | _ => none).map KernelStaticDiagnostic.kernelCode |>.getD (oneLine ((repr error).pretty 100000)) }

/-- The resolved common precondition and every alternative's own guard, kept apart because the
tables judge an alternative's guardedness by its own guard alone. -/
private def guards (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) (suppress : Bool) :
    Lowering (Option (CheckedComputationCondition model) × List (Option (CheckedComputationCondition model))) := do
  let resolve (text : String) : Lowering (CheckedComputationCondition model) := do
    let surface ← guardSurface language model computation target suppress text
    (model.elaborateCheckedComputationCondition computation.group target.groupPath surface).mapError guardRefusal
  let common ← computation.commonPrecondition.mapM resolve
  let own ← computation.alternatives.mapM (·.precondition.mapM resolve)
  pure (common, own)

/-- Every alternative's guard, with the common precondition distributed, checked against the
instance view of the target's joined groups. -/
private def joinedGuards (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) (suppress : Bool) : Lowering (List (Option (ParallelNumericGuard model))) := do
  let joined := model.parallelJoinedGroups target
  let view := model.parallelInstanceView joined
  -- Each leaf is lowered and checked against the view and against the model, because the view drops
  -- the repetition and index of every joined group: a starred, keyed or filtered read of one only
  -- exists against the model, at the target row or, keyed by a partner field, at a partner row.
  let partners := joined.filter fun group => !group.isPrefixOf target.groupPath
  let rec tree : Expr → Lowering (ConditionTree (ParallelNumericGuardPart model joined))
    | .parens body => tree body
    | .logic op (first :: rest) => do
        let join := match op with
          | .and => ConditionTree.and
          | .or => ConditionTree.or
        let mut result ← tree first
        for part in rest do result := join result (← tree part)
        pure result
    | leaf => ParallelNumericGuardPart.choose
        (do
          let surface ← lowerGuard view computation.group suppress leaf (some target.groupPath)
          (model.elaborateParallelNumericGuardLeaf joined computation.group target.groupPath surface).mapError guardRefusal)
        (do
          let surface ← lowerGuard model computation.group suppress leaf (some target.groupPath)
          (model.elaborateCheckedComputationCondition computation.group target.groupPath surface).mapError guardRefusal)
        (partners.map fun group => (group, do
          let surface ← lowerGuard model computation.group suppress leaf (some group)
          (model.elaborateCheckedComputationCondition computation.group group surface).mapError guardRefusal))
      |>.map .leaf
  let resolve (text : String) : Lowering (ConditionTree (ParallelNumericGuardPart model joined)) := do
    let guard := (← parsed language text).body
    if !guard.parensLegal true then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    tree guard
  let common ← computation.commonPrecondition.mapM resolve
  let own ← computation.alternatives.mapM (·.precondition.mapM resolve)
  let withCommon := fun (guard : Option (ConditionTree (ParallelNumericGuardPart model joined))) =>
    match common, guard with
    | none, guard => guard
    | some common, none => some common
    | some common, some guard => some (.and common guard)
  pure (own.map fun guard => (withCommon guard).map ({ joined, condition := · }))

/-- Reuse the checked parallel carriers after ordinary scope binding refuses. The complete table owns
its joined routes, including scalar fallbacks; bound fields retain the ordinary target environment. -/
private def lowerParallelNumber (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) (expressions : List (AuthoredNumericExpr SurfaceNumericComputationAtom))
    (suppress : Bool) (outputModes : List (Option ComputationRoundingMode)) :
    Lowering (CheckedParallelNumericStep model) := do
  let group := computation.group
  let _ ← elaborated "ParallelNumber" (checkAddressedRepeatableTarget model group target.id)
  if computation.alternatives.length > 1 && computation.alternatives.any (·.precondition.isNone) then
    refuse "ParallelNumber" "unguarded alternative"
  let guards ← joinedGuards language model computation target suppress
  -- The checked run enforces the same ban; the reader names its Kernel class (g12 of the
  -- parallel-guard capture, 2026-10-14).
  if guards.any (·.any (·.forbidsTarget target.id)) then
    refuse "ParallelGuard" KernelStaticDiagnostic.errorReferenceToCalculatedField.kernelCode
  if expressions.length != outputModes.length then refuse "ParallelNumber" "output policy arity"
  -- An atom with no joined form, such as a starred aggregate, keeps its ordinary meaning at the
  -- target row (joined-carrier capture, row `j11`, 2026-10-14).
  let expressions ← expressions.mapM fun expression => expression.mapM fun atom =>
    match atom.parallelAtom? with
    | some atom => pure (ParallelNumericOperationAtomOf.joined atom)
    | none => .ordinary <$> elaborated "ParallelNumber"
        (model.elaborateNumericComputationAtom group target.groupPath atom)
  let guardFields := guards.flatMap parallelNumericGuardFields
  let guardPaths := guardFields.filterMap fun field => (model.lookupUniqueId field).toOption.map fun declaration =>
    { base := .absolute, groups := declaration.groupPath, field := declaration.name : SurfaceFieldPath }
  let fields := expressions.flatMap (fun expression =>
    (expression.atoms.filterMap (·.joined?)).flatMap SurfaceNumericAtom.parallelFields) ++ guardPaths
  let some operand := fields.find? fun path => (checkParallelNumericTargetRoute model group target.id path).isOk
    | refuse "ParallelNumber" "no joined operand"
  let operations ← ((guards.zip expressions).zip outputModes).mapM fun ((guard, expression), mode) => do
    let operation ← elaborated "ParallelNumber" (checkParallelNumericTableOperationWithGuard model group
      target.id operand expression guard suppress)
    pure (operation.withBandedRounding mode)
  match operations with
  | [operation] => pure (.single operation)
  | _ => (.alternatives ·) <$> elaborated "ParallelNumber" (certifyParallelNumericAlternativeTable operations)

/-- A String or temporal row target whose operation reads a partner row. The joined Number carrier's
key joins and guards carry over; the operation is checked against the instance view, where each joined
group is a fixed group, so the ordinary row elaborators read a partner field as a fixed read
(joined-carrier capture, rows `t01`–`t03`, 2026-10-14). -/
private def lowerJoinedRows (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) (operations : List Expr) (suppress : Bool) :
    Lowering (CheckedParallelJoinedRowStep model) := do
  let group := computation.group
  let _ ← elaborated "ParallelRows" (checkAddressedRepeatableTarget model group target.id)
  if computation.alternatives.length > 1 && computation.alternatives.any (·.precondition.isNone) then
    refuse "ParallelRows" "unguarded alternative"
  let guards ← joinedGuards language model computation target suppress
  if guards.any (·.any (·.forbidsTarget target.id)) then
    refuse "ParallelGuard" KernelStaticDiagnostic.errorReferenceToCalculatedField.kernelCode
  let joined := model.parallelJoinedGroups target
  let view := model.parallelInstanceView joined
  let some viewTarget := (view.lookupUniqueId target.id).toOption | refuse "ParallelRows" "target"
  let operations ← operations.mapM fun expression => do
    match ← lowerRowAlternativeOperation view group viewTarget expression suppress with
    | .stringExpression operation => pure (ParallelJoinedRowOperation.string operation)
    | .temporalExpression operation => pure (.temporal operation)
    | _ => refuse "ParallelRows" "operation"
  let alternatives := (guards.zip operations).map fun (precondition, operation) =>
    ({ precondition, operation } : ParallelJoinedRowAlternative model joined)
  elaborated "ParallelRows" (checkParallelJoinedRowStep model group target.id joined alternatives)

inductive LoweredComputation (model : FlatModel)
  | number (table : CheckedNumericComputationTable model) (row : Bool)
  | parallel (step : CheckedParallelNumericStep model)
  | string (table : CheckedStringComputationTable model)
  | document (step : CheckedDocumentComputationStep model)
  /-- A non-Number computation over addressed instances, including fixed Boolean/Confirm tables. -/
  | rows (step : RowStep model)
  | joinedRows (step : CheckedParallelJoinedRowStep model)

/-- The plan step a lowered computation runs as. -/
def LoweredComputation.toMixedStep (compilePattern : StringPatternCompiler) :
    LoweredComputation model → MixedComputationStep model compilePattern
  | .number table _ => .number table
  | .parallel step => .parallel step
  | .string table => .string table
  | .document step => .document step
  | .rows step => .rows (step compilePattern)
  | .joinedRows step => .joinedRows step

private def computationOutputModes (computation : DmComputation) :
    Lowering (List (Option ComputationRoundingMode)) := do
  let mode ← match computation.roundingMode with
    | "Exact" => pure ComputationRoundingMode.exact
    | "RoundUp" => pure .roundUp
    | "RoundDown" => pure .roundDown
    | _ => refuse "RoundingMode" "unknown mode"
  computation.alternatives.mapM fun alternative => do
    let banded ← match alternative.toleranceRangeOp with
      | none => pure false
      | some "DiffersWithToleranceRange1" | some "DiffersWithToleranceRange2"
      | some "DiffersWithToleranceRange5" | some "DiffersWithToleranceRange10" => pure true
      | some _ => refuse "ToleranceRange" "unknown range"
    if !mode.admitted banded then refuse "RoundingMode" "MVK_ERROR_WRONG_ROUNDING_MODE"
    pure (if banded then some mode else none)

/-- Constructor/filter-containing computations need the joined condition's complete parse-time admission
before its global checks. Fragments remain error values until their authored turn, so a later parse or
read failure cannot pre-empt an earlier operation/comparison (spec/09 §6). -/
private def checkComputationOrderedAdmission (language : Language) (model : FlatModel)
    (computation : DmComputation) (target : FlatFieldDecl) (suppress : Bool) : Lowering Unit := do
  let fragment (condition : Bool) (text : String) : Lowering Expr := do
    let body := (← parsed language text).body
    if !body.parensLegal condition then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    pure body
  let common := computation.commonPrecondition.map (fragment true)
  let alternatives := computation.alternatives.map fun alternative =>
    (alternative.precondition.map (fragment true), fragment false alternative.operation, alternative.toleranceRangeOp)
  let projected := fun (source : Lowering Expr) => source.toOption.any fun expression =>
    expression.hasProjectedReferenceTo model computation.group target.id
  let ordered := fun (source : Lowering Expr) =>
    source.toOption.any Expr.needsOrderedAdmission || projected source
  if !common.any ordered && !alternatives.any (fun (guard, operation, _) => guard.any ordered || ordered operation) then return
  let check := checkRawConditionBeforeGlobals model computation.group target.groupPath
  let mut facts : FilterRuleFacts := {}
  if let some common := common then facts := facts.merge (← check (← common) suppress)
  for (guard, operation, tolerance) in alternatives do
    if let some guard := guard then facts := facts.merge (← check (← guard) suppress)
    checkRawComputationTargetRead model computation.group target
    let operation ← operation
    let comparison ← match tolerance with
      | none => pure CompareOp.ne
      | some "DiffersWithToleranceRange1" => pure (.tolerance 1)
      | some "DiffersWithToleranceRange2" => pure (.tolerance 2)
      | some "DiffersWithToleranceRange5" => pure (.tolerance 5)
      | some "DiffersWithToleranceRange10" => pure (.tolerance 10)
      | some _ => refuse "ToleranceRange" "unknown range"
    facts := facts.merge (← check (.compare comparison (rawComputationTarget target) operation) suppress)
  -- The generated filled-target conjunction is not a standalone raw-Length limiter (spec/09 §6).
  if let some diagnostic := facts.beforeIterationRefusal? then refuse "Having" diagnostic.kernelCode
  -- The projected class precedes alternative-table checks even for an unconditional alternative
  -- or an otherwise unjudged common precondition (spec/09 §6; self-read-alternative-walk grid).
  if common.any projected || alternatives.any (fun (guard, operation, _) =>
      guard.any projected || projected operation) then
    refuse "Computation" KernelStaticDiagnostic.errorSemanticIndexOrCategoryForErrorField.kernelCode

private def lowerComputationWith (allowParallelGuards : Bool)
    (model : FlatModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model) := do
  let target ← targetOf language model computation
  let texts := computation.commonPrecondition.toList ++ computation.alternatives.flatMap
    (fun alternative => alternative.precondition.toList ++ [alternative.operation])
  let hasHaving := texts.any fun text => (parseText language text).toOption.any (·.body.hasHaving)
  let readOutputModes := do
    let modes ← computationOutputModes computation
    if target.policy.kind.surfaceKind != .number && modes.any Option.isSome then
      refuse "ToleranceRange" "non-Number target"
    pure modes
  -- Delay caller compatibility only for the complete filter preflight; unfiltered callers
  -- retain their existing admission boundary (H08's scope in docs/gaps/paths-and-groups.md).
  let earlyModes ← if hasHaving then pure none else some <$> readOutputModes
  let suppression : Lowering (List String) := if computation.errorCodesToSuppress.isEmpty then pure [] else
    (·.suppressed) <$> parsed language
      s!"@SuppressWarning({",".intercalate computation.errorCodesToSuppress}) 0"
  let validatedSuppression : Lowering Bool := do
    let suppressed ← suppression
    if suppressed.any (· != "MVK_INVALID_COMPARE_DEC_PLACES") then
      refuse "SuppressWarning" KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode
    pure (suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES")
  -- Filter preflight starts at the generated preamble (spec/09 §6; spec/12 §4).
  -- The unfiltered route defers preamble failures until guards and operation syntax finish.
  let suppress ← if hasHaving then validatedSuppression else
    pure ((suppression.toOption.getD []).contains "MVK_INVALID_COMPARE_DEC_PLACES")
  checkComputationOrderedAdmission language model computation target suppress
  -- Calculation-mode compatibility follows the generated condition’s parser gates (spec/09 §6).
  let outputModes ← match earlyModes with | some modes => pure modes | none => readOutputModes
  -- A guard the ordinary reader refused can only belong to the joined Number route.
  let (common, guards) ← if allowParallelGuards then pure (none, [])
    else guards language model computation target suppress
  let operations ← computation.alternatives.mapM fun alternative => do
    let body := (← parsed language alternative.operation).body
    if !body.parensLegal false then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    pure body
  let suppress ← if hasHaving then pure suppress else validatedSuppression
  let row := !target.repeatableScope.isEmpty
  let numericExpressions := operations.mapM fun expression => do
    let filterBinding? := if expression.hasHaving then some target.groupPath else none
    let atom := fun operand => lowerCompleteComputationNumericAtom model computation.group operand filterBinding? suppress
    lowerNumericExpr atom (lowerNumericFieldAtom model computation.group atom) expression
  if allowParallelGuards then
    if !row then refuse "Guard" "joined route"
    let .number _ := target.policy.kind
      | return (target, .joinedRows (← lowerJoinedRows language model computation target operations suppress))
    return (target, .parallel (← lowerParallelNumber language model computation target
      (← numericExpressions) suppress outputModes))
  let document : Lowering (FlatFieldDecl × LoweredComputation model) := do
    if let ([own], [operation]) := (guards, operations) then
      let step ← lowerDocumentStep model computation.group target suppress operation
      let step ← match CheckedComputationCondition.withCommon common own with
        | none => pure step
        | some guard => (step.guard? guard).getDM (refuse "DocumentStep" "guard admission")
      pure (target, .document step)
    else
      let alternatives ← (guards.zip operations).mapM fun (precondition, expression) => do
        let operation ← lowerDocumentStep model computation.group target suppress expression
        pure ({ precondition, operation := .document operation } : CheckedComputationAlternative model _)
      let table ← elaborated "DocumentStep" (certifyRowComputationTable alternatives common)
      let step ← (CheckedRowComputationStep.ofTable? table).getDM (refuse "DocumentStep" "target self-read")
      pure (target, .rows step)
  if (row || operations.any (fun | .call "FirstFilledValue" _ none none => true | _ => false) || (target.policy.kind == .string && operations.any (fun expression =>
      (lowerSelectedStringExpr model computation.group expression).toOption.any fun source =>
        source.fields.any fun | .inr _ => true | .inl _ => false)) || target.policy.kind == .boolean || target.policy.kind == .confirm || target.policy.kind == .enumeration || target.policy.kind == .dateRange ||
      (target.temporalTargetPolicy.isSome && operations.length > 1)) &&
      operations.all (isRowAlternativeOperation model computation.group target) then
    let ordinary : Lowering (RowStep model) := do
      let alternatives ← (guards.zip operations).mapM fun (precondition, expression) => do
        let operation ← lowerRowAlternativeOperation model computation.group target expression suppress
        pure ({ precondition, operation } : CheckedComputationAlternative model _)
      let table ← elaborated "RowComputation" (certifyRowComputationTable alternatives common)
      let some step := CheckedRowComputationStep.ofTable? table
        | refuse "RowComputation" "target self-read"
      pure step
    -- An operation reading a partner row is refused ordinarily and admitted through its key join;
    -- a failed join keeps the ordinary refusal.
    match ordinary with
    | .ok step => return (target, .rows step)
    | .error refusal =>
        match lowerJoinedRows language model computation target operations suppress with
        | .ok step => return (target, .joinedRows step)
        | .error _ => throw refusal
  match target.policy.kind with
  | .number _ => do
      let expressions ← numericExpressions
      match elaborated "NumberComputation"
          (elaborateCompleteNumericTargetComputationTable model computation.group target.id
            (guards.zip expressions) suppress (if row then .row else .fixed) common) with
      | .ok table => do
          let table ← (table.withBandedRounding? outputModes).getDM (refuse "NumberComputation" "output policy arity")
          pure (target, .number table row)
      | .error refusal =>
          match lowerParallelNumber language model computation target expressions suppress outputModes with
          | .ok step => pure (target, .parallel step)
          | .error parallel => .error (refusal.orGuardBan parallel)
  | .string => do
      if row then
        let (none, [none], [operation]) := (common, guards, operations)
          | refuse "StringComputation" "row target"
        return (target, .rows (← lowerRowStep model computation.group target suppress operation))
      if operations.any fun | .call "FirstFilledValue" _ none none => true | _ => false then
        return ← document
      let attempts : List (Option (CheckedComputationCondition model) ×
          Except (Sum Refusal StringComputationElabError) (CheckedStringComputationOperation model)) :=
        (guards.zip operations).map fun (precondition, operation) =>
          (precondition, do
            let expression ← (lowerStringExpr operation).mapError Sum.inl
            (elaborateStringComputationOperation model computation.group target.id expression).mapError Sum.inr)
      let table ← match certifyStringComputationTableFromAttempts model target.id attempts
          (fun | .inr (.targetSelfReference _) => true | _ => false) common with
        | .ok table => pure table
        | .error (.operation _ (.inl refusal)) => .error refusal
        | .error (.operation _ (.inr error)) => elaborated "StringComputation" (.error error)
        | .error (.table error) => elaborated "StringComputation" (.error error)
      pure (target, .string table)
  | kind =>
      if !row then
        return ← document
      else if let (none, [none], [operation]) := (common, guards, operations) then
        match lowerRowStep model computation.group target suppress operation with
        | .ok step => return (target, .rows step)
        -- A carrier's own refusal names the gate; an operation no row carrier names meets the generic one.
        | .error refusal => if refusal.construct != "RowComputation" then throw refusal
      let name := match kind.surfaceKind with
        | .number => "Number" | .boolean => "Boolean" | .confirm => "Confirm" | .string => "String"
        | .enumeration => "Enumeration" | .dateRange => "DateRange"
        | .temporal .date => "Date" | .temporal .time => "Time" | .temporal .dateTime => "DateTime"
      refuse s!"{name}Computation" (operations.head?.map (·.construct) |>.getD "")

/-- Lower one computation onto its checked carrier. A parallel guard contributes admission only
when the complete computation checks; a failed fallback keeps the original guard refusal unless
the joined route reached its guard's target ban. -/
def lowerComputation (model : FlatModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model) := do
  admitDeclarations [computation.declaration]
  match lowerComputationWith false model language computation with
  | .ok checked => .ok checked
  | .error refusal =>
      if refusal.construct != "Guard" then .error refusal
      else match lowerComputationWith true model language computation with
        | .ok checked => .ok checked
        | .error parallel => .error (refusal.orGuardBan parallel)

private def numberOutcome (model : FlatModel) (entry : SourcedNumericTargetOutcome CellAddr) :
    Option ComputedOutcome :=
  let pointer := renderPointer model (MessagePointer.ofCellAddr entry.targetField)
  match NumericComputationRunView.changedInstance? entry, NumericComputationRunView.computedError? entry with
  | some changed, _ => some { pointer, outcome := s!"value {changed.value.render}" }
  | none, some failed => some { pointer, outcome := s!"errored {failed.attempted.render}" }
  | none, none =>
      if NumericComputationRunView.shouldClear entry then some { pointer, outcome := "cleared" } else none

/-- The text an errored whole-document target attempted. -/
private def documentAttempt? : DocumentTargetOutcome → Option String
  | .dateTime (.errored attempted _) | .fullDate (.errored attempted _)
  | .dateRange (.errored attempted _) => some attempted.text
  | .enumeration (.errored attempted _) | .dateFragment (.errored attempted _)
  | .string (.errored attempted _) => some attempted.text
  | _ => none

/-- The change projection of one String or whole-document outcome at its address: an unchanged value
is no change, and a target that held a value and now holds none is cleared. -/
private def textOutcome (model : FlatModel) (checked : CheckedDocument model) (address : CellAddr)
    (value? errored? : Option String) : Option ComputedOutcome :=
  let pointer := renderPointer model (MessagePointer.ofCellAddr address)
  let stored := (checked.storedTextAt address).getD ""
  let unconverted := checked.source.cells.any fun cell =>
    cell.address == address && cell.sourceRepresentation == .unconvertedText
  let retainsTextIdentity := match (model.fields.find? (·.id == address.field)).map (·.policy.kind) with
    | some .string | some .enumeration => true
    | _ => !unconverted
  match value?, errored? with
  | some value, _ => if retainsTextIdentity && value == stored then none else some { pointer, outcome := s!"value {value}" }
  | none, some attempted => some { pointer, outcome := s!"errored {attempted}" }
  | none, none => if !stored.isEmpty then some { pointer, outcome := "cleared" } else none

/-- Assemble one checked call before projecting the lowered computations' changes. -/
def runComputations (world : World) (prepared : PreparedFlatStringContext model compilePattern)
    (checked : CheckedDocument model) (lowered : List (LoweredComputation model)) :
    Lowering (List ComputedOutcome) := do
  let steps := lowered.map (·.toMixedStep compilePattern)
  let plan ← elaborated "ComputationPlan" (certifyAuthoredMixedComputationPlan steps)
  let result ← elaborated "ComputationRun" (plan.executeResultWithFormalInputs world prepared.patterns checked)
  pure (result.outcomes.filterMap fun
    | .number entry => numberOutcome model entry
    | .string target (.accepted value) => textOutcome model checked { field := target, path := [] }
        (some value.text) none
    | .string target (.errored attempted _) => textOutcome model checked { field := target, path := [] }
        none (some attempted.text)
    | .string target _ => textOutcome model checked { field := target, path := [] } none none
    | .document address outcome => textOutcome model checked address outcome.storedText?
        (documentAttempt? outcome))

end A12Kernel.Dm
