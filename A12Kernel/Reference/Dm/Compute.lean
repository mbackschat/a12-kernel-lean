import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Reference.Dm.LowerRows
import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.MixedComputationPlan

/-! # Running a DM model's computations over one document

Each computation is parsed and lowered onto the checked table of its target's kind, which joins its
common precondition onto every alternative, or refused by the construct no carrier admits. The lowered
steps, Number and String tables, whole-document targets and repeatable String constants, are certified
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
  -- The path is written from the element, one step below its group; a relative path without that
  -- step is outside every retained model, so it is refused rather than read at the group.
  if !path.absolute && path.ups == 0 then refuse "Target" computation.targetRelPath
  let relative := if path.absolute then path else { path with ups := path.ups - 1 }
  let some field := relative.toFieldPath? | refuse "Target" computation.targetRelPath
  elaborated "Target" (model.resolveFieldDeclarationUnchecked computation.group field)

/-- The resolved common precondition and every alternative's own guard, kept apart because the
tables judge an alternative's guardedness by its own guard alone. -/
private def guards (language : Language) (model : FlatModel) (computation : DmComputation)
    (target : FlatFieldDecl) :
    Lowering (Option ComputationCondition × List (Option ComputationCondition)) := do
  let resolve (text : String) : Lowering ComputationCondition := do
    let guard := (← parsed language text).body
    if !guard.parensLegal true then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    let surface ← lowerGuard guard
    elaborated "Guard" (model.elaborateComputationCondition computation.group target.groupPath surface)
  let common ← computation.commonPrecondition.mapM resolve
  let own ← computation.alternatives.mapM (·.precondition.mapM resolve)
  pure (common, own)

inductive LoweredComputation (model : FlatModel)
  | number (table : CheckedNumericComputationTable model) (row : Bool)
  | string (table : CheckedStringComputationTable model)
  | document (step : CheckedDocumentComputationStep model)
  /-- A computation into a repeatable target of a kind other than Number, run at every row. -/
  | rows (step : RowStep model)

/-- Lower one computation onto its target kind's checked table. -/
def lowerComputation (model : FlatModel) (language : Language) (computation : DmComputation) :
    Lowering (FlatFieldDecl × LoweredComputation model) := do
  let target ← targetOf language model computation
  let (common, guards) ← guards language model computation target
  let operations ← computation.alternatives.mapM fun alternative => do
    let body := (← parsed language alternative.operation).body
    if !body.parensLegal false then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    pure body
  if let some other := computation.errorCodesToSuppress.find? (· != "MVK_INVALID_COMPARE_DEC_PLACES") then
    refuse "SuppressWarning" other
  let suppress := computation.errorCodesToSuppress.contains "MVK_INVALID_COMPARE_DEC_PLACES"
  let row := !target.repeatableScope.isEmpty
  -- A whole-document step carries one operation and no precondition.
  let document : Lowering (FlatFieldDecl × LoweredComputation model) := do
    let (none, [none], [operation]) := (common, guards, operations)
      | refuse "DocumentStep" "precondition or alternatives"
    pure (target, .document (← lowerDocumentStep model computation.group target operation))
  match target.policy.kind with
  | .number _ => do
      let expressions ← operations.mapM
        (lowerNumericExpr (lowerComputationNumericAtom model computation.group))
      let table ← elaborated "NumberComputation"
        (elaborateCompleteNumericTargetComputationTable model computation.group target.id
          (guards.zip expressions) suppress (if row then .row else .fixed) common)
      pure (target, .number table row)
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
        pure ({ precondition, operation := checked } : ComputationAlternative _)
      pure (target, .string (← elaborated "StringComputation" (certifyStringComputationTable alternatives common)))
  | kind =>
      if !row then
        if let .ok lowered := document then return lowered
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
    | .string table => .string table
    | .document step => .document step
    | .rows step => .rows (step compilePattern)
  let plan ← elaborated "ComputationPlan" (certifyMixedComputationPlan steps)
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
