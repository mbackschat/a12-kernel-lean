import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.ScalarComputationRun

/-! # Running a DM model's computations over one document

Each computation is parsed and lowered onto the checked table of its target's kind, with its common
precondition joined onto every alternative. The tables then run on one of the two executors that
exist: the repeatable Number plan, which addresses fixed and row targets, when every lowered target
is a Number, and otherwise the scalar plan, which runs String and Number targets at fixed addresses
only. Every other target kind, a row target beside a String target, and every operation no carrier
admits is refused by construct.

The result is projected onto what a Kernel `compute` observation reports: its change projection,
an instance whose computed value equals its stored value being no change, a target that held a
value and now holds none being cleared, and a rejected attempt being errored. The Number plan
supplies that projection itself (`NumericComputationRunView`); for the scalar plan's String targets
it is taken against the stored text.
-/

namespace A12Kernel.Dm

/-- One reported computation outcome: `value <text>`, `cleared` or `errored <text>`. -/
structure ComputedOutcome where
  pointer : String
  outcome : String
  deriving Repr, BEq, Ord, Inhabited

instance : ToString ComputedOutcome where
  toString computed := s!"{computed.pointer}={computed.outcome}"

/-- A computation guard: fill checks under `And` and `Or`, all a computation precondition admits. -/
partial def lowerGuard : Expr → Lowering SurfaceComputationCondition
  | .parens body => lowerGuard body
  | .logic op (first :: rest) => do
      let join := match op with
        | .and => SurfaceComputationCondition.and
        | .or => SurfaceComputationCondition.or
      let mut result ← lowerGuard first
      for part in rest do result := join result (← lowerGuard part)
      pure result
  | .call "FieldFilled" [.mk field none none] none none => match field.fieldEntity? with
      | some path => pure (.fieldFilled path)
      | none => refuse "Guard" "FieldFilled operand"
  | .call "FieldNotFilled" [.mk field none none] none none => match field.fieldEntity? with
      | some path => pure (.fieldNotFilled path)
      | none => refuse "Guard" "FieldNotFilled operand"
  | other => refuse ("Guard/" ++ other.construct)

/-- A String computation's operation: field reads, literals, `FieldValueAsString`, `RangeAsString`
and `+` concatenation. -/
partial def lowerStringExpr : Expr → Lowering (StringExpr SurfaceFieldPath)
  | .string text => pure (.literal text)
  | .value { path, index := none, category := none } => match path.toFieldPath? with
      | some field => pure (.field field)
      | none => refuse "StringOperand" "path"
  | .call "FieldValueAsString" [.mk field none none] none none => match field.fieldEntity? with
      | some path => pure (.fieldValueAsString path)
      | none => refuse "FieldValueAsString" "operand"
  | .call "RangeAsString" [.mk field none none, .mk (.number start) none none,
      .mk (.number finish) none none] none none =>
      match field.fieldEntity?, start.toNat?, finish.toNat? with
      | some path, some start, some finish => pure (.range path start finish)
      | _, _, _ => refuse "RangeAsString" "operand"
  | .arith .add left right => do pure (.concat (← lowerStringExpr left) (← lowerStringExpr right))
  | .braces body => lowerStringExpr body
  | other => refuse ("StringOperation/" ++ other.construct)

private def parsed (language : Language) (text : String) : Lowering Text :=
  match parseText language text with
  | .ok text => pure text
  | .error error => refuse "Syntax" error.errorClass.code

/-- The declaration a computation targets. Its path is relative to the computation element. -/
def targetOf (language : Language) (model : FlatModel) (computation : DmComputation) :
    Lowering FlatFieldDecl := do
  let text ← parsed language computation.targetRelPath
  let some path := match text.body with
      | .entity { path, index := none, category := none } => some path
      | _ => none
    | refuse "Target" computation.targetRelPath
  let relative := if path.absolute then path else { path with ups := path.ups - 1 }
  let some field := relative.toFieldPath? | refuse "Target" computation.targetRelPath
  elaborated "Target" (model.resolveFieldDeclarationUnchecked computation.group field)

/-- The resolved guards of every alternative with the common precondition joined on. -/
private def guards (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) : Lowering (List (Option ComputationCondition)) := do
  let resolve (text : String) : Lowering ComputationCondition := do
    let surface ← lowerGuard (← parsed language text).body
    elaborated "Guard" (model.elaborateComputationCondition computation.group target.groupPath surface)
  let common ← computation.commonPrecondition.mapM resolve
  let own ← computation.alternatives.mapM (·.precondition.mapM resolve)
  pure ((ComputationAlternative.expandCommonPrecondition common
    (own.map fun precondition => ({ precondition, operation := () } : ComputationAlternative Unit))).map
      (·.precondition))

inductive LoweredComputation (model : FlatModel)
  | number (table : CheckedNumericComputationTable model) (row : Bool)
  | string (table : CheckedStringComputationTable model)
  | document (step : CheckedDocumentComputationStep model)

/-- Lower one computation onto its target kind's checked table. -/
def lowerComputation (model : FlatModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model) := do
  let target ← targetOf language model computation
  let guards ← guards language model computation target
  let operations ← computation.alternatives.mapM fun alternative => do
    pure (← parsed language alternative.operation).body
  let suppress := computation.errorCodesToSuppress.contains "MVK_INVALID_COMPARE_DEC_PLACES"
  let row := !target.repeatableScope.isEmpty
  -- A whole-document step carries one operation and no precondition.
  let document : Lowering (FlatFieldDecl × LoweredComputation model) := do
    let ([none], [operation]) := (guards, operations)
      | refuse "DocumentStep" "precondition or alternatives"
    pure (target, .document (← lowerDocumentStep model computation.group target operation))
  match target.policy.kind with
  | .number _ => do
      let expressions ← operations.mapM
        (lowerNumericExpr (lowerComputationNumericAtom model computation.group))
      let table ← elaborated "NumberComputation"
        (elaborateCompleteNumericTargetComputationTable model computation.group target.id
          (guards.zip expressions) suppress (if row then .row else .fixed))
      pure (target, .number table row)
  | .string => do
      if row then refuse "StringComputation" "row target"
      if operations.any fun | .call "FirstFilledValue" _ none none => true | _ => false then
        return ← document
      let alternatives ← (guards.zip operations).mapM fun (precondition, operation) => do
        let expression ← lowerStringExpr operation
        let checked ← elaborated "StringComputation"
          (elaborateStringComputationOperation model computation.group target.id expression)
        pure ({ precondition, operation := checked } : ComputationAlternative _)
      pure (target, .string (← elaborated "StringComputation" (certifyStringComputationTable alternatives)))
  | kind =>
      if !row then
        if let .ok lowered := document then return lowered
      let name := match kind.surfaceKind with
        | .number => "Number" | .boolean => "Boolean" | .confirm => "Confirm" | .string => "String"
        | .enumeration => "Enumeration" | .dateRange => "DateRange"
        | .temporal .date => "Date" | .temporal .time => "Time" | .temporal .dateTime => "DateTime"
      refuse s!"{name}Computation" (operations.head?.map (·.construct) |>.getD "")

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

/-- Run the lowered computations and project their change outcomes. -/
def runComputations (world : World) (prepared : PreparedFlatStringContext model compilePattern)
    (checked : CheckedDocument model) (lowered : List (LoweredComputation model)) :
    Lowering (List ComputedOutcome) := do
  let numbers := lowered.filterMap fun | .number table _ => some table | _ => none
  if numbers.length == lowered.length then
    let plan ← elaborated "ComputationPlan" (certifyRepeatableNumberPlan numbers)
    let outcomes ← elaborated "ComputationRun" (plan.execute world checked)
    pure (outcomes.filterMap (numberOutcome model))
  else
    if lowered.any fun | .number _ true => true | _ => false then
      refuse "ComputationRun" "a row Number target beside a String target"
    let steps := lowered.map fun
      | .number table _ => CheckedScalarComputationStep.number table
      | .string table => .string table
      | .document step => .document step
    let plan ← elaborated "ComputationPlan" (certifyScalarComputationPlan steps)
    let outcomes ← elaborated "ComputationRun" (plan.execute world prepared.patterns checked)
    pure (outcomes.filterMap fun outcome =>
      let (target, value?, cleared, errored?) := match outcome with
        | .string target (.accepted value) => (target, some value.text, false, none)
        | .string target (.errored attempted _) => (target, none, false, some attempted.text)
        | .string target _ => (target, none, true, none)
        | .number target (.accepted value) => (target, some value.render, false, none)
        | .number target (.rejected attempted _) => (target, none, false, some attempted.render)
        | .number target _ => (target, none, true, none)
        | .document target outcome => (target, outcome.storedText?, outcome.storedText?.isNone &&
            (documentAttempt? outcome).isNone, documentAttempt? outcome)
      let address : CellAddr := { field := target, path := [] }
      let pointer := renderPointer model (MessagePointer.ofCellAddr address)
      let stored := (checked.storedTextAt address).getD ""
      match value?, errored? with
      | some value, _ => if value == stored then none else some { pointer, outcome := s!"value {value}" }
      | none, some attempted => some { pointer, outcome := s!"errored {attempted}" }
      | none, none => if cleared && !stored.isEmpty then some { pointer, outcome := "cleared" } else none)

end A12Kernel.Dm
