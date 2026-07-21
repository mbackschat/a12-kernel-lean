import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.NumericTolerance

/-! # Checked numeric validation

This capsule connects two model-resolved nonrepeatable Number expressions to the existing authored-scale, one-pass lowering, arithmetic-fillability, ordinary-comparison, and fixed-tolerance semantics. It admits plain arithmetic plus separately audited direct-field root value functions in the evaluated row group; general operation-wrapper traversal remains excluded. Its structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing and that decoder contract remain outside this module.
-/

namespace A12Kernel

/-- Parser-independent input to the checked numeric consumer. -/
structure SurfaceNumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr SurfaceFieldPath
  right : AuthoredNumericExpr SurfaceFieldPath
  deriving Repr, DecidableEq

/-- Resolved runtime representation; static guarantees belong to `CheckedNumericComparison`. -/
structure NumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr FlatNumberField
  right : AuthoredNumericExpr FlatNumberField
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

private def AuthoredNumericExpr.hasAtom : AuthoredNumericExpr Atom → Bool
  | .atom _ => true
  | .literal _ => false
  | .group body => body.hasAtom
  | .binary _ left right | .power left right | .extremum _ left right =>
      left.hasAtom || right.hasAtom
  | .abs body => body.hasAtom
  | .round _ _ body => body.hasAtom

/-- Whether an authored tree uses only atoms, literals, grouping, ordinary binary arithmetic, and power. -/
def AuthoredNumericExpr.isPlainArithmetic : AuthoredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .group body => body.isPlainArithmetic
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .round _ _ _ => false

def AuthoredNumericExpr.isDirectAtom : AuthoredNumericExpr Atom → Bool
  | .atom _ => true
  | _ => false

/-- Canonical left fold of one authored operand list, restricted to direct fields and one selector. The concrete decoder must construct this form from the nonempty source list. -/
def AuthoredNumericExpr.isDirectFieldExtremumChain
    (expected : NumericExtremumOp) : AuthoredNumericExpr Atom → Bool
  | .atom _ => true
  | .extremum actual left right =>
      (actual == expected) &&
        left.isDirectFieldExtremumChain expected && right.isDirectAtom
  | _ => false

/-- The checked value-function shapes: one root rounding or absolute-value operation over a direct Number field, or one canonical direct-field Min/Max fold. Expression and `…Value` surface spellings normalize to these same semantic nodes. -/
def AuthoredNumericExpr.isDirectFieldValueFunction : AuthoredNumericExpr Atom → Bool
  | .abs (.atom _) => true
  | .round _ _ (.atom _) => true
  | .extremum op left right =>
      left.isDirectFieldExtremumChain op && right.isDirectAtom
  | _ => false

/-- The checked validation fragment is plain arithmetic plus independently audited root value functions. -/
def AuthoredNumericExpr.isAdmittedValidation : AuthoredNumericExpr Atom → Bool
  | expression => expression.isPlainArithmetic || expression.isDirectFieldValueFunction

/-- General operation-wrapper traversal remains unclosed; only exact direct-field root functions bypass the plain-arithmetic authoring scan. -/
def AuthoredNumericExpr.validationAuthoringCheck
    (expression : AuthoredNumericExpr Atom) : NumericAuthoringCheck :=
  if expression.isDirectFieldValueFunction then .accepted else expression.authoringCheck

private def AuthoredNumericExpr.allAtoms (predicate : Atom → Bool) :
    AuthoredNumericExpr Atom → Bool
  | .atom sourceAtom => predicate sourceAtom
  | .literal _ => true
  | .group body => body.allAtoms predicate
  | .binary _ left right | .power left right =>
      left.allAtoms predicate && right.allAtoms predicate
  | .extremum _ left right =>
      left.allAtoms predicate && right.allAtoms predicate
  | .abs body => body.allAtoms predicate
  | .round _ _ body => body.allAtoms predicate

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
        comparison.op.acceptsScales leftSummary rightSummary
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
      Except NumericValidationElabError (AuthoredNumericExpr FlatNumberField)
  | .atom reference => do
      let declaration ←
        (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toNumberField? with
      | some field => pure (.atom field)
      | none => throw (.fieldNotNumber declaration.path)
  | .literal literal => pure (.literal literal)
  | .group body => do
      pure (.group (← resolveNumericExpression model rowGroup body))
  | .binary op left right => do
      pure (.binary op
        (← resolveNumericExpression model rowGroup left)
        (← resolveNumericExpression model rowGroup right))
  | .power base exponent => do
      pure (.power
        (← resolveNumericExpression model rowGroup base)
        (← resolveNumericExpression model rowGroup exponent))
  | .abs body => do
      pure (.abs (← resolveNumericExpression model rowGroup body))
  | .extremum op left right => do
      pure (.extremum op
        (← resolveNumericExpression model rowGroup left)
        (← resolveNumericExpression model rowGroup right))
  | .round mode places body => do
      pure (.round mode places (← resolveNumericExpression model rowGroup body))

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
      if !surface.op.acceptsScales leftSummary rightSummary then
        throw (.exactScaleMismatch leftSummary rightSummary)
      let core : NumericComparison := { op := surface.op, left, right }
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

def LoweredNumericExpr.isDirectAtom : LoweredNumericExpr Atom → Bool
  | .atom _ => true
  | _ => false

def LoweredNumericExpr.isDirectFieldExtremumChain
    (expected : NumericExtremumOp) : LoweredNumericExpr Atom → Bool
  | .atom _ => true
  | .extremum actual left right =>
      (actual == expected) &&
        left.isDirectFieldExtremumChain expected && right.isDirectAtom
  | _ => false

/-- Lowering preserves the checked direct-field root-function shapes exactly. -/
def LoweredNumericExpr.isDirectFieldValueFunction : LoweredNumericExpr Atom → Bool
  | .abs (.atom _) => true
  | .round _ _ (.atom _) => true
  | .extremum op left right =>
      left.isDirectFieldExtremumChain op && right.isDirectAtom
  | _ => false

def LoweredNumericExpr.isAdmittedValidation : LoweredNumericExpr Atom → Bool
  | expression => expression.isPlainArithmetic || expression.isDirectFieldValueFunction

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

private def NumericExtremumOp.selectValidationOutcome (op : NumericExtremumOp) :
    Except FormalCause NumericArithmeticOutcome →
      Except FormalCause NumericArithmeticOutcome →
        Except FormalCause NumericArithmeticOutcome
  | left, right =>
      combineNumericValidationOutcomes op.selectOutcome left right

/-- Evaluate the canonical left fold for one direct-field numeric operand list. `none` rejects a mixed selector, a literal, or any nested non-field expression. -/
def LoweredNumericExpr.evalDirectFieldExtremum?
    (expected : NumericExtremumOp)
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Option (Except FormalCause NumericArithmeticOutcome)
  | .atom sourceAtom => some (read sourceAtom)
  | .extremum actual left (.atom rightAtom) =>
      if actual == expected then do
        let leftOutcome ← left.evalDirectFieldExtremum? expected read
        pure (expected.selectValidationOutcome leftOutcome (read rightAtom))
      else
        none
  | _ => none

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
      expression.evalDirectFieldExtremum? op read
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
