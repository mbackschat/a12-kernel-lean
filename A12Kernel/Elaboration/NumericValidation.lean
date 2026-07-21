import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.NumericTolerance

/-! # Checked numeric validation

This capsule connects two model-resolved nonrepeatable Number expressions to the existing authored-scale, one-pass lowering, arithmetic-fillability, ordinary-comparison, and fixed-tolerance semantics. It admits plain arithmetic plus separately audited root value functions in the evaluated row group; operand-list extrema may contain direct fields and at most one top-level constant. General operation-wrapper traversal remains excluded. Its structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing and that decoder contract remain outside this module.
-/

namespace A12Kernel

/-- Parser-independent input to the checked numeric consumer. -/
structure SurfaceNumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr SurfaceFieldPath
  right : AuthoredNumericExpr SurfaceFieldPath
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Resolved runtime representation; static guarantees belong to `CheckedNumericComparison`. -/
structure NumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr FlatNumberField
  right : AuthoredNumericExpr FlatNumberField
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Closed rejection classes for this deliberately narrow consumer, not kernel diagnostic codes. -/
inductive NumericValidationElabError where
  | resolve (error : ResolveError)
  | fieldOutsideRowGroup (path : List String) (rowGroup : GroupPath)
  | fieldNotNumber (path : List String)
  | constantExpression
  | unsupportedExpression
  | authoring (result : NumericAuthoringCheck)
  | exactScaleMismatch (left right : NumericScaleSummary)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether an authored tree uses only atoms, literals, grouping, ordinary binary arithmetic, and power. -/
def AuthoredNumericExpr.isPlainArithmetic : AuthoredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .group body => body.isPlainArithmetic
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .round _ _ _ => false

/-- Recognize one canonical left-associated extremum operand list while tracking whether its single permitted direct constant has been consumed. `none` rejects mixed selectors, a second constant, wrappers, grouping, or a non-direct right operand. -/
def AuthoredNumericExpr.directExtremumConstantUse?
    (expected : NumericExtremumOp) :
    AuthoredNumericExpr Atom → Option Bool
  | .atom _ => some false
  | .literal _ => some true
  | .extremum actual left right =>
      if actual != expected then none else do
        let constantUsed ← left.directExtremumConstantUse? expected
        match right with
        | .atom _ => some constantUsed
        | .literal _ => if constantUsed then none else some true
        | _ => none
  | _ => none

def AuthoredNumericExpr.isDirectExtremumChain
    (expected : NumericExtremumOp) (expression : AuthoredNumericExpr Atom) : Bool :=
  (expression.directExtremumConstantUse? expected).isSome

/-- The checked value-function shapes: one root rounding or absolute-value operation over a direct Number field, or one canonical direct-operand Min/Max fold with at most one constant. Expression and `…Value` surface spellings normalize to these same semantic nodes. -/
def AuthoredNumericExpr.isDirectValueFunction : AuthoredNumericExpr Atom → Bool
  | .abs (.atom _) => true
  | .round _ _ (.atom _) => true
  | expression@(.extremum op _ _) => expression.isDirectExtremumChain op
  | _ => false

/-- The checked validation fragment is plain arithmetic plus independently audited root value functions. -/
def AuthoredNumericExpr.isAdmittedValidation : AuthoredNumericExpr Atom → Bool
  | expression => expression.isPlainArithmetic || expression.isDirectValueFunction

/-- General operation-wrapper traversal remains unclosed; only exact direct-field root functions bypass the plain-arithmetic authoring scan. -/
def AuthoredNumericExpr.validationAuthoringCheck
    (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  if expression.isDirectValueFunction then .accepted else expression.authoringCheck

private def FlatModel.admitsNumberInGroup (model : FlatModel) (rowGroup : GroupPath)
    (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.groupPath == rowGroup &&
        declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some field
  | .error _ => false

/-- Ordering is scale-exempt; unsuppressed equality and inequality use the exact authored-scale gate. -/
def NumericComparisonOp.acceptsScales (op : NumericComparisonOp)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .equal | .notEqual => exactNumericScaleComparisonAllowed left right
  | .less | .lessEqual | .greater | .greaterEqual => true

/-- Tolerance deliberately bypasses the ordinary exact-comparison scale gate. -/
def NumericValidationOp.acceptsScales (op : NumericValidationOp)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .ordinary comparison => comparison.acceptsScales left right
  | .tolerance _ => true

/-- The one legal parser warning suppression bypasses only the exact-comparison scale gate. Every other authoring check remains independent. -/
def NumericValidationOp.acceptsScalesWithSuppression
    (op : NumericValidationOp) (suppressExactScaleWarning : Bool)
    (left right : NumericScaleSummary) : Bool :=
  suppressExactScaleWarning || op.acceptsScales left right

def NumericComparison.wellFormedBool
    (comparison : NumericComparison)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  (comparison.left.hasAtom || comparison.right.hasAtom) &&
    comparison.left.isAdmittedValidation &&
    comparison.right.isAdmittedValidation &&
    comparison.left.allAtoms (model.admitsNumberInGroup rowGroup) &&
    comparison.right.allAtoms (model.admitsNumberInGroup rowGroup) &&
    comparison.left.validationAuthoringCheck == .accepted &&
    comparison.right.validationAuthoringCheck == .accepted &&
    match
        comparison.left.summary? (fun field =>
          NumericScaleSummary.field field.info.scale),
        comparison.right.summary? (fun field =>
          NumericScaleSummary.field field.info.scale) with
    | some leftSummary, some rightSummary =>
        comparison.op.acceptsScalesWithSuppression
          comparison.suppressExactScaleWarning leftSummary rightSummary
    | _, _ => false

def NumericComparison.WellFormed
    (comparison : NumericComparison)
    (model : FlatModel) (rowGroup : GroupPath) : Prop :=
  comparison.wellFormedBool model rowGroup = true

/-- A model-coherent numeric comparison produced only after every static stage succeeds. -/
structure CheckedNumericComparison (model : FlatModel) where
  rowGroup : GroupPath
  core : NumericComparison
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model rowGroup

private def resolveNumericExpression (model : FlatModel) (rowGroup : GroupPath) :
    AuthoredNumericExpr SurfaceFieldPath →
      Except NumericValidationElabError (AuthoredNumericExpr FlatNumberField) :=
  AuthoredNumericExpr.mapM fun reference => do
      let declaration ←
        (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toNumberField? with
      | some field => pure field
      | none => throw (.fieldNotNumber declaration.path)

/-- Resolve and check both operands before performing their one-pass lowering at evaluation time. -/
def elaborateNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedNumericComparison model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let left ← resolveNumericExpression model rowGroup surface.left
      let right ← resolveNumericExpression model rowGroup surface.right
      if !(left.hasAtom || right.hasAtom) then throw .constantExpression
      if !left.isAdmittedValidation then throw .unsupportedExpression
      if !right.isAdmittedValidation then throw .unsupportedExpression
      match left.validationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      match right.validationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      let leftSummary ← match left.summary? (fun field =>
          NumericScaleSummary.field field.info.scale) with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      let rightSummary ← match right.summary? (fun field =>
          NumericScaleSummary.field field.info.scale) with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      if !surface.op.acceptsScalesWithSuppression
          surface.suppressExactScaleWarning leftSummary rightSummary then
        throw (.exactScaleMismatch leftSummary rightSummary)
      let core : NumericComparison := {
        op := surface.op
        left
        right
        suppressExactScaleWarning := surface.suppressExactScaleWarning }
      if hCore : core.wellFormedBool model rowGroup = true then
        pure {
          rowGroup
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

/-- Lift the existing validation-phase Number read into the arithmetic outcome domain. -/
def FlatContext.resolveNumericArithmetic (context : FlatContext)
    (field : FlatNumberField) : Except FormalCause NumericArithmeticOutcome :=
  match context.resolveNumberComparisonOperand field with
  | .value amount fillability => .ok (.value amount fillability)
  | .unknown cause => .error cause

private def combineNumericValidationOutcomes
    (combine : NumericArithmeticOutcome → NumericArithmeticOutcome →
      NumericArithmeticOutcome)
    (left right : Except FormalCause NumericArithmeticOutcome) :
    Except FormalCause NumericArithmeticOutcome :=
  match left, right with
  | .error cause, _ => .error cause
  | _, .error cause => .error cause
  | .ok leftOutcome, .ok rightOutcome => .ok (combine leftOutcome rightOutcome)

private def evalPlainBinary (op : NumericScaleBinaryOp)
    (left right : Except FormalCause NumericArithmeticOutcome) :
    Except FormalCause NumericArithmeticOutcome :=
  combineNumericValidationOutcomes
    (fun leftOutcome rightOutcome =>
      match op with
        | .add => NumericArithmeticOutcome.eval .add leftOutcome rightOutcome
        | .subtract => NumericArithmeticOutcome.eval .subtract leftOutcome rightOutcome
        | .multiply => NumericArithmeticOutcome.eval .multiply leftOutcome rightOutcome
        | .divide => NumericArithmeticOutcome.divide leftOutcome rightOutcome)
    left right

/-- Whether a lowered tree lies in the consumer's binary-arithmetic runtime subset. -/
def LoweredNumericExpr.isPlainArithmetic : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .round _ _ _ => false

/-- Runtime-shape mirror of the authored canonical extremum list. -/
def LoweredNumericExpr.directExtremumConstantUse?
    (expected : NumericExtremumOp) :
    LoweredNumericExpr Atom → Option Bool
  | .atom _ => some false
  | .literal _ => some true
  | .extremum actual left right =>
      if actual != expected then none else do
        let constantUsed ← left.directExtremumConstantUse? expected
        match right with
        | .atom _ => some constantUsed
        | .literal _ => if constantUsed then none else some true
        | _ => none
  | _ => none

def LoweredNumericExpr.isDirectExtremumChain
    (expected : NumericExtremumOp) (expression : LoweredNumericExpr Atom) : Bool :=
  (expression.directExtremumConstantUse? expected).isSome

/-- Lowering preserves the checked direct root-function shapes exactly. -/
def LoweredNumericExpr.isDirectValueFunction : LoweredNumericExpr Atom → Bool
  | .abs (.atom _) => true
  | .round _ _ (.atom _) => true
  | expression@(.extremum op _ _) => expression.isDirectExtremumChain op
  | _ => false

def LoweredNumericExpr.isAdmittedValidation : LoweredNumericExpr Atom → Bool
  | expression => expression.isPlainArithmetic || expression.isDirectValueFunction

/-- Evaluate the plain validation subset; `none` marks a wrapper outside this helper's responsibility. -/
def LoweredNumericExpr.evalPlainValidation?
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Option (Except FormalCause NumericArithmeticOutcome)
  | .atom sourceAtom => some (read sourceAtom)
  | .literal amount => some (.ok (.value amount .fixed))
  | .binary op left right => do
      let leftOutcome ← left.evalPlainValidation? read
      let rightOutcome ← right.evalPlainValidation? read
      pure (evalPlainBinary op leftOutcome rightOutcome)
  | .power base exponent => do
      let baseOutcome ← base.evalPlainValidation? read
      let exponentOutcome ← exponent.evalPlainValidation? read
      pure (combineNumericValidationOutcomes NumericArithmeticOutcome.power
        baseOutcome exponentOutcome)
  | .abs _ | .extremum _ _ _ | .round _ _ _ => none

/-- Preserve the first formal cause across exact extremum selection of two reached validation outcomes. -/
def NumericExtremumOp.selectValidationOutcome (op : NumericExtremumOp) :
    Except FormalCause NumericArithmeticOutcome →
      Except FormalCause NumericArithmeticOutcome →
        Except FormalCause NumericArithmeticOutcome
  | left, right =>
      combineNumericValidationOutcomes op.selectOutcome left right

/-- Evaluate the canonical left fold while returning the same direct-constant usage bit as the runtime shape check. -/
def LoweredNumericExpr.evalDirectExtremumWithConstantUse?
    (expected : NumericExtremumOp)
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    LoweredNumericExpr Atom →
      Option (Except FormalCause NumericArithmeticOutcome × Bool)
  | .atom sourceAtom => some (read sourceAtom, false)
  | .literal amount => some (.ok (.value amount .fixed), true)
  | .extremum actual left right =>
      if actual != expected then none else do
        let (leftOutcome, constantUsed) ←
          left.evalDirectExtremumWithConstantUse? expected read
        match right with
        | .atom rightAtom =>
            some (expected.selectValidationOutcome leftOutcome (read rightAtom),
              constantUsed)
        | .literal amount =>
            if constantUsed then none else
              some (expected.selectValidationOutcome leftOutcome
                (.ok (.value amount .fixed)), true)
        | _ => none
  | _ => none

/-- Evaluate one admitted canonical extremum list and erase its checked constant-usage state. -/
def LoweredNumericExpr.evalDirectExtremum?
    (expected : NumericExtremumOp)
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
    Option (Except FormalCause NumericArithmeticOutcome) :=
  (expression.evalDirectExtremumWithConstantUse? expected read).map Prod.fst

/-- Evaluate exactly the checked runtime fragment. Value functions are admitted only at the root over a direct field; their result-domain maps preserve formal invalidity and arithmetic domain failure. -/
def LoweredNumericExpr.evalAdmittedValidation?
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Option (Except FormalCause NumericArithmeticOutcome)
  | .round mode places (.atom sourceAtom) =>
      some <| match read sourceAtom with
        | .ok outcome => .ok (outcome.round mode places)
        | .error cause => .error cause
  | .abs (.atom sourceAtom) =>
      some <| match read sourceAtom with
        | .ok outcome => .ok outcome.absolute
        | .error cause => .error cause
  | expression@(.extremum op _ _) =>
      expression.evalDirectExtremum? op read
  | expression => expression.evalPlainValidation? read

/-- Evaluate a raw core. The unknown fallback fails closed for a forged unsupported operand and is unreachable through the checked route. -/
def NumericComparison.evalSelected
    (comparison : NumericComparison) (context : FlatContext) : Verdict :=
  match
      comparison.left.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericArithmetic,
      comparison.right.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericArithmetic with
  | some left, some right => comparison.op.evalArithmetic left right
  | _, _ => .unknown

/-- Evaluate one already row-selected checked comparison. -/
def CheckedNumericComparison.evalSelected
    (checked : CheckedNumericComparison model)
    (context : FlatContext) : Verdict :=
  checked.core.evalSelected context

/-- An admitted comparison never fires on an entirely blank full-validation row. -/
def CheckedNumericComparison.evalFull
    (checked : CheckedNumericComparison model)
    (context : FlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then checked.evalSelected context else .notFired

/-- Check a surface comparison and evaluate it against model-derived cells under full validation. -/
def elaborateAndEvalNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError Verdict := do
  let checked ← elaborateNumericComparison model rowGroup surface
  pure (checked.evalFull (model.checkContext raw) hasContent)

end A12Kernel
