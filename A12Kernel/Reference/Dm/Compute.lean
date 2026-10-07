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
  | .entity { path, index := none, category } => do
      let field ← path.toFieldPath?
      pure (match category with | none => .direct field | some name => .category field name)
  | _ => none

private def lowerScalarMembership (operator : ValueListMembershipOp)
    (arguments : List Argument) : Lowering SurfaceComputationPredicate := do
  let .mk subject none none :: members := arguments | refuse "Guard/Membership" "subject"
  let some subject := scalarMembershipSubject? subject | refuse "Guard/Membership" "bare subject"
  let some members := members.mapM (fun | .mk expr none none => some expr | _ => none)
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
  let .value { path, index, category := none } := left | refuse "Guard/Pattern" "field value"
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
  match expression with
  | .custom _ _ => refuse "CustomCondition" "not admitted in computation guards"
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
  | .call "FieldFilled" [.mk (.entity { path, index := some key, category := none }) none none] none none =>
      (.predicate ∘ .indexedFieldPresence .filled) <$> lowerIndexedSource model group path key
  | .call "FieldNotFilled" [.mk (.entity { path, index := some key, category := none }) none none] none none =>
      (.predicate ∘ .indexedFieldPresence .notFilled) <$> lowerIndexedSource model group path key
  | .call "FieldFilled" [.mk field none none] none none => match field.fieldEntity? with
      | some path => pure (.fieldFilled path)
      | none => refuse "Guard" "FieldFilled operand"
  | .call "FieldNotFilled" [.mk field none none] none none => match field.fieldEntity? with
      | some path => pure (.fieldNotFilled path)
      | none => refuse "Guard" "FieldNotFilled operand"
  | .call "GroupFilled" [argument@(.mk (.entity { index := some _, .. }) none none)] none none => do
      let .keyed source ← lowerEntityOperand model group argument | refuse "Guard/GroupFilled" "group operand"
      pure (.predicate (.keyedGroupPresence .filled source))
  | .call "GroupNotFilled" [argument@(.mk (.entity { index := some _, .. }) none none)] none none => do
      let .keyed source ← lowerEntityOperand model group argument | refuse "Guard/GroupNotFilled" "group operand"
      pure (.predicate (.keyedGroupPresence .notFilled source))
  | .call "GroupFilled" [.mk group none none] none none => match group.groupReference? with
      | some reference => pure (.groupPresence .filled reference)
      | none => refuse "Guard/GroupFilled" "group operand"
  | .call "GroupNotFilled" [.mk group none none] none none => match group.groupReference? with
      | some reference => pure (.groupPresence .notFilled reference)
      | none => refuse "Guard/GroupNotFilled" "group operand"
  | .call "Valid" [.mk (.call "Date" arguments none none) none none] none none =>
      (.predicate ∘ .dateValidity .valid) <$> lowerScalarDateComponents model group arguments
  | .call "Invalid" [.mk (.call "Date" arguments none none) none none] none none =>
      (.predicate ∘ .dateValidity .invalid) <$> lowerScalarDateComponents model group arguments
  | .call "Valid" [.mk (.entity { path, index := some key, category := none }) none none, .mk (.string name) none none] none none => do
      pure (.predicate (.indexedTypeValidity .valid (← lowerIndexedSource model group path key) name))
  | .call "Invalid" [.mk (.entity { path, index := some key, category := none }) none none, .mk (.string name) none none] none none => do
      pure (.predicate (.indexedTypeValidity .invalid (← lowerIndexedSource model group path key) name))
  | .call "Valid" [.mk field none none, .mk (.string name) none none] none none => do
      let some path := field.fieldEntity? | refuse "ValidType" "field operand"
      pure (.predicate (.typeValidity .valid path name))
  | .call "Invalid" [.mk field none none, .mk (.string name) none none] none none => do
      let some path := field.fieldEntity? | refuse "InvalidType" "field operand"
      pure (.predicate (.typeValidity .invalid path name))
  | .call "FieldValuesNotUnique" arguments none none =>
      (.predicate ∘ .uniqueness) <$> lowerEntitySource model group arguments
  | .call "DateRangesOverlap" arguments none none =>
      (.predicate ∘ .overlap) <$> lowerEntitySource model group arguments
  | .call "AtLeastOneDateRangeOverlaps" [scalar] (some values) none => do
      pure (.predicate (.scalarOverlap {
        scalar := ← lowerEntityOperand model group scalar
        list := ← lowerEntitySource model group values }))
  | .call id arguments (some values) none => do
      let some quantifier := valueListQuantifier? id | refuse ("Guard/" ++ id)
      let fields ← lowerEntitySource model group arguments
      match values.mapM (fun | .mk (.string value) none none => some value | _ => none) with
      | some literals => pure (.predicate (.tokenLiteralValueList { quantifier, fields, values := literals }))
      | none => pure (.predicate (.entityValueList {
          quantifier, fields, values := ← lowerEntitySource model group values }))
  | .call id arguments none none => match scalarMembershipOp? id with
      | some operator => .predicate <$> lowerScalarMembership operator arguments
      | none => match fieldFillOp? id with
          | some operator => .fieldFill operator <$> lowerEntitySource model group arguments
          | none => match groupQuantifier? id with
              | some operator => .groupFill operator <$> lowerEntitySource model group arguments
              | none => refuse ("Guard/" ++ id)
  | expression@(.compare op left right) =>
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
      let temporalSurface := do
        let operator ← op.toSurface?
        let left ← (lowerScalarTemporalExpression model group left).toOption
        let right ← (lowerScalarTemporalExpression model group right).toOption
        match elaborateScalarTemporalComparison model group operator.toTemporal left right targetGroup? with
        | .error (.nonTemporal _) | .error (.extremum (.firstNotTemporal _ _)) => none
        | _ => some (SurfaceComputationConditionOf.predicate
            (SurfaceComputationPredicate.temporal operator.toTemporal left right))
      match (textSurface.orElse (fun _ => stringSurface)).orElse (fun _ => temporalSurface) with
      | some surface => pure surface
      | none => do
          let some operator := op.toNumeric? | refuse "Comparison" "operator"
          pure (.numeric {
            op := operator
            left := ← lowerNumericExpr (lowerCompleteComputationNumericAtom model group) (lowerNumericFieldAtom model group (lowerCompleteComputationNumericAtom model group)) left
            right := ← lowerNumericExpr (lowerCompleteComputationNumericAtom model group) (lowerNumericFieldAtom model group (lowerCompleteComputationNumericAtom model group)) right
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

/-- The resolved common precondition and every alternative's own guard, kept apart because the
tables judge an alternative's guardedness by its own guard alone. -/
private def guards (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) (suppress allowParallel : Bool) :
    Lowering (Option (CheckedComputationCondition model) × List (Option (CheckedComputationCondition model))) := do
  let resolve (text : String) : Lowering (CheckedComputationCondition model) := do
    let guard := (← parsed language text).body
    if !guard.parensLegal true then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    let surface ← lowerGuard model computation.group suppress guard (some target.groupPath)
    match elaborated "Guard" (model.elaborateCheckedComputationCondition computation.group target.groupPath surface) with
    | .ok guard => pure guard
    | .error refusal =>
        if allowParallel && target.toNumberField?.isSome && !target.repeatableScope.isEmpty then
          let rec presenceSurface : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate →
              Option SurfaceComputationCondition
            | .fieldFilled field => some (.fieldFilled field)
            | .fieldNotFilled field => some (.fieldNotFilled field)
            | .and left right => do pure (.and (← presenceSurface left) (← presenceSurface right))
            | .or left right => do pure (.or (← presenceSurface left) (← presenceSurface right))
            | _ => none
          let some legacy := presenceSurface surface | .error refusal
          match model.resolveParallelPresenceCondition computation.group legacy with
          | .ok guard => elaborated "Guard" (CheckedComputationCondition.ofLegacy model guard)
          | .error _ => .error refusal
        else .error refusal
  let common ← computation.commonPrecondition.mapM resolve
  let own ← computation.alternatives.mapM (·.precondition.mapM resolve)
  pure (common, own)

/-- Reuse the checked parallel carriers after ordinary scope binding refuses. Each operation must
retain a joined Number operand; bound fields use the same target environment as the ordinary route. -/
private def lowerParallelNumber (model : FlatModel) (group : GroupPath) (target : FieldId)
    (guards : List (Option (CheckedComputationCondition model)))
    (expressions : List (AuthoredNumericExpr SurfaceNumericComputationAtom))
    (common : Option (CheckedComputationCondition model)) (suppress : Bool) :
    Lowering (CheckedParallelNumericStep model) := do
  let _ ← elaborated "ParallelNumber" (checkAddressedRepeatableTarget model group target)
  if guards.length > 1 && guards.any Option.isNone then refuse "ParallelNumber" "unguarded alternative"
  let operations ← (guards.zip expressions).mapM fun (guard, expression) => do
    let expression ← expression.mapM fun
      | .numeric (.field path) => pure (SurfaceNumericAtom.field path)
      | _ => refuse "ParallelNumber" "operand"
    let fields := expression.atoms.filterMap fun | .field path => some path | _ => none
    let some operand := fields.find? fun path =>
        (checkParallelNumericComputationClearingPlan model group target path).isOk
      | refuse "ParallelNumber" "no joined operand"
    elaborated "ParallelNumber" (checkIsolatedParallelNumericExpressionRunWithGuard model group
      target operand expression (CheckedComputationCondition.withCommon common guard) suppress)
  match operations with
  | [operation] => pure (.single operation)
  | _ => (.alternatives ·) <$> elaborated "ParallelNumber" (certifyParallelNumericAlternativeTable operations)

inductive LoweredComputation (model : FlatModel)
  | number (table : CheckedNumericComputationTable model) (row : Bool)
  | parallel (step : CheckedParallelNumericStep model)
  | string (table : CheckedStringComputationTable model)
  | document (step : CheckedDocumentComputationStep model)
  /-- A non-Number computation over addressed instances, including fixed Boolean/Confirm tables. -/
  | rows (step : RowStep model)

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

private def lowerComputationWith (allowParallelGuards : Bool)
    (model : FlatModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model) := do
  let target ← targetOf language model computation
  let outputModes ← computationOutputModes computation
  if target.policy.kind.surfaceKind != .number && outputModes.any Option.isSome then
    refuse "ToleranceRange" "non-Number target"
  -- Decode once for guard scale admission, but retain the reader's guard/operation/refusal order.
  let suppression : Lowering (List String) :=
    if computation.errorCodesToSuppress.isEmpty then pure [] else
      (·.suppressed) <$> parsed language
        s!"@SuppressWarning({",".intercalate computation.errorCodesToSuppress}) 0"
  let guardSuppress := (suppression.toOption.getD []).contains "MVK_INVALID_COMPARE_DEC_PLACES"
  let (common, guards) ← guards language model computation target guardSuppress allowParallelGuards
  let operations ← computation.alternatives.mapM fun alternative => do
    let body := (← parsed language alternative.operation).body
    if !body.parensLegal false then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    pure body
  -- The entries reach the parser joined into one preamble (spec §12.4), so padding is admitted
  -- and a second name is a parse failure, as in a rule's own text.
  let suppressed ← suppression
  if let some other := suppressed.find? (· != "MVK_INVALID_COMPARE_DEC_PLACES") then
    refuse "SuppressWarning" other
  let suppress := suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES"
  let row := !target.repeatableScope.isEmpty
  -- The checked step already owns guard evaluation; the reader preserves its single-operation boundary.
  let document : Lowering (FlatFieldDecl × LoweredComputation model) := do
    let ([own], [operation]) := (guards, operations)
      | refuse "DocumentStep" "alternatives"
    let step ← lowerDocumentStep model computation.group target operation
    let step ← match CheckedComputationCondition.withCommon common own with
      | none => pure step
      | some guard => (step.guard? guard).getDM (refuse "DocumentStep" "guard admission")
    pure (target, .document step)
  if (row || (target.policy.kind == .string && operations.any (fun expression =>
      (lowerSelectedStringExpr model computation.group expression).toOption.any fun source =>
        source.fields.any fun | .inr _ => true | .inl _ => false)) || target.policy.kind == .boolean || target.policy.kind == .confirm || target.policy.kind == .dateRange ||
      (target.temporalTargetPolicy.isSome && operations.length > 1)) &&
      operations.all (isRowAlternativeOperation model computation.group target) then
    let alternatives ← (guards.zip operations).mapM fun (precondition, expression) => do
      let operation ← lowerRowAlternativeOperation model computation.group target expression
      pure ({ precondition, operation } : CheckedComputationAlternative model _)
    let table ← elaborated "RowComputation" (certifyRowComputationTable alternatives common)
    let some step := CheckedRowComputationStep.ofTable? table
      | refuse "RowComputation" "target self-read"
    return (target, .rows step)
  match target.policy.kind with
  | .number _ => do
      let expressions ← operations.mapM
        (lowerNumericExpr (lowerCompleteComputationNumericAtom model computation.group) (lowerNumericFieldAtom model computation.group (lowerCompleteComputationNumericAtom model computation.group)))
      match elaborated "NumberComputation"
          (elaborateCompleteNumericTargetComputationTable model computation.group target.id
            (guards.zip expressions) suppress (if row then .row else .fixed) common) with
      | .ok table => do
          let table ← (table.withBandedRounding? outputModes).getDM (refuse "NumberComputation" "output policy arity")
          pure (target, .number table row)
      | .error refusal =>
          if outputModes.any Option.isSome then throw refusal
          match lowerParallelNumber model computation.group target.id guards expressions common suppress with
          | .ok step => pure (target, .parallel step)
          | .error _ => .error refusal
  | .string => do
      if row then
        let (none, [none], [operation]) := (common, guards, operations)
          | refuse "StringComputation" "row target"
        return (target, .rows (← lowerRowStep model computation.group target operation))
      if operations.any fun | .call "FirstFilledValue" _ none none => true | _ => false then
        return ← document
      let alternatives ← (guards.zip operations).mapM fun (precondition, operation) => do
        let expression ← lowerStringExpr operation
        let checked ← elaborated "StringComputation"
          (elaborateStringComputationOperation model computation.group target.id expression)
        pure ({ precondition, operation := checked } : CheckedComputationAlternative model _)
      pure (target, .string (← elaborated "StringComputation" (certifyStringComputationTable alternatives common)))
  | kind =>
      if !row then
        return ← document
      else if let (none, [none], [operation]) := (common, guards, operations) then
        match lowerRowStep model computation.group target operation with
        | .ok step => return (target, .rows step)
        -- A carrier's own refusal names the gate; an operation no row carrier names meets the generic one.
        | .error refusal => if refusal.construct != "RowComputation" then throw refusal
      let name := match kind.surfaceKind with
        | .number => "Number" | .boolean => "Boolean" | .confirm => "Confirm" | .string => "String"
        | .enumeration => "Enumeration" | .dateRange => "DateRange"
        | .temporal .date => "Date" | .temporal .time => "Time" | .temporal .dateTime => "DateTime"
      refuse s!"{name}Computation" (operations.head?.map (·.construct) |>.getD "")

/-- Lower one computation onto its checked carrier. A parallel guard contributes admission only
when the complete computation checks; failed fallback preserves the original guard refusal. -/
def lowerComputation (model : FlatModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model) :=
  match lowerComputationWith false model language computation with
  | .ok checked => .ok checked
  | .error refusal =>
      if refusal.construct != "Guard" then .error refusal
      else match lowerComputationWith true model language computation with
        | .ok checked => .ok checked
        | .error _ => .error refusal

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
  match value?, errored? with
  | some value, _ => if value == stored then none else some { pointer, outcome := s!"value {value}" }
  | none, some attempted => some { pointer, outcome := s!"errored {attempted}" }
  | none, none => if !stored.isEmpty then some { pointer, outcome := "cleared" } else none

/-- Run the lowered computations on one plan and project their change outcomes. -/
def runComputations (world : World) (prepared : PreparedFlatStringContext model compilePattern)
    (checked : CheckedDocument model) (lowered : List (LoweredComputation model)) :
    Lowering (List ComputedOutcome) := do
  let steps : List (MixedComputationStep model compilePattern) := lowered.map fun
    | .number table _ => .number table
    | .parallel step => .parallel step
    | .string table => .string table
    | .document step => .document step
    | .rows step => .rows (step compilePattern)
  let plan ← elaborated "ComputationPlan" (certifyAuthoredMixedComputationPlan steps)
  let outcomes ← elaborated "ComputationRun" (plan.execute world prepared.patterns checked)
  pure (outcomes.filterMap fun
    | .number entry => numberOutcome model entry
    | .string target (.accepted value) => textOutcome model checked { field := target, path := [] }
        (some value.text) none
    | .string target (.errored attempted _) => textOutcome model checked { field := target, path := [] }
        none (some attempted.text)
    | .string target _ => textOutcome model checked { field := target, path := [] } none none
    | .document address outcome => textOutcome model checked address outcome.storedText?
        (documentAttempt? outcome))

end A12Kernel.Dm
