import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression

/-! # Checked fixed-right numeric validation

This capsule connects model-resolved nonrepeatable Number atoms to the existing authored-scale, one-pass lowering, arithmetic-fillability, and fixed-right comparison semantics. It deliberately admits only plain arithmetic in the evaluated row group. Its structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing and that decoder contract remain outside this module.
-/

namespace A12Kernel

/-- Parser-independent input to the checked fixed-right consumer. -/
structure SurfaceNumericFixedRightComparison where
  op : NumericComparisonOp
  left : AuthoredNumericExpr SurfaceFieldPath
  right : DecodedNumericLiteral
  deriving Repr, DecidableEq

/-- Resolved runtime representation; static guarantees belong to `CheckedNumericFixedRightComparison`. -/
structure NumericFixedRightComparison where
  op : NumericComparisonOp
  left : AuthoredNumericExpr FlatNumberField
  right : DecodedNumericLiteral
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
  | .binary _ left right | .power left right => left.hasAtom || right.hasAtom
  | .round _ _ body => body.hasAtom

/-- Whether an authored tree uses only atoms, literals, grouping, and ordinary binary arithmetic. -/
def AuthoredNumericExpr.isPlainArithmetic : AuthoredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .group body => body.isPlainArithmetic
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power _ _ | .round _ _ _ => false

private def AuthoredNumericExpr.allAtoms (predicate : Atom → Bool) :
    AuthoredNumericExpr Atom → Bool
  | .atom sourceAtom => predicate sourceAtom
  | .literal _ => true
  | .group body => body.allAtoms predicate
  | .binary _ left right | .power left right =>
      left.allAtoms predicate && right.allAtoms predicate
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
def NumericComparisonOp.acceptsFixedRightScales (op : NumericComparisonOp)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .equal | .notEqual => exactNumericScaleComparisonAllowed left right
  | .less | .greaterEqual => true

def NumericFixedRightComparison.wellFormedBool
    (comparison : NumericFixedRightComparison)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  comparison.left.hasAtom &&
    comparison.left.isPlainArithmetic &&
    comparison.left.allAtoms (model.admitsNumberInGroup rowGroup) &&
    comparison.left.authoringCheck == .accepted &&
    match comparison.left.summary? (fun field =>
        NumericScaleSummary.field field.info.scale) with
    | some leftSummary =>
        comparison.op.acceptsFixedRightScales leftSummary
          (NumericScaleSummary.constant comparison.right.authoredScale)
    | none => false

def NumericFixedRightComparison.WellFormed
    (comparison : NumericFixedRightComparison)
    (model : FlatModel) (rowGroup : GroupPath) : Prop :=
  comparison.wellFormedBool model rowGroup = true

/-- A model-coherent fixed-right comparison produced only after every static stage succeeds. -/
structure CheckedNumericFixedRightComparison (model : FlatModel) where
  rowGroup : GroupPath
  core : NumericFixedRightComparison
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
  | .round mode places body => do
      pure (.round mode places (← resolveNumericExpression model rowGroup body))

/-- Resolve and check the supported surface before performing the one-pass lowering at evaluation time. -/
def elaborateNumericFixedRight (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericFixedRightComparison) :
    Except NumericValidationElabError (CheckedNumericFixedRightComparison model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let left ← resolveNumericExpression model rowGroup surface.left
      if !left.hasAtom then throw .constantExpression
      if !left.isPlainArithmetic then throw .unsupportedExpression
      match left.authoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      let leftSummary ← match left.summary? (fun field =>
          NumericScaleSummary.field field.info.scale) with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      let rightSummary := NumericScaleSummary.constant surface.right.authoredScale
      if !surface.op.acceptsFixedRightScales leftSummary rightSummary then
        throw (.exactScaleMismatch leftSummary rightSummary)
      let core : NumericFixedRightComparison :=
        { op := surface.op, left, right := surface.right }
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

private def evalPlainBinary (op : NumericScaleBinaryOp)
    (left right : Except FormalCause NumericArithmeticOutcome) :
    Except FormalCause NumericArithmeticOutcome :=
  match left, right with
  | .error cause, _ => .error cause
  | _, .error cause => .error cause
  | .ok leftOutcome, .ok rightOutcome =>
      .ok <| match op with
        | .add => NumericArithmeticOutcome.eval .add leftOutcome rightOutcome
        | .subtract => NumericArithmeticOutcome.eval .subtract leftOutcome rightOutcome
        | .multiply => NumericArithmeticOutcome.eval .multiply leftOutcome rightOutcome
        | .divide => NumericArithmeticOutcome.divide leftOutcome rightOutcome

/-- Whether a lowered tree lies in the consumer's binary-arithmetic runtime subset. -/
def LoweredNumericExpr.isPlainArithmetic : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power _ _ | .round _ _ _ => false

/-- Evaluate the plain validation subset; `none` is reserved for power or rounding and is unreachable for a checked comparison. -/
def LoweredNumericExpr.evalPlainValidation?
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Option (Except FormalCause NumericArithmeticOutcome)
  | .atom sourceAtom => some (read sourceAtom)
  | .literal amount => some (.ok (.value amount .fixed))
  | .binary op left right => do
      let leftOutcome ← left.evalPlainValidation? read
      let rightOutcome ← right.evalPlainValidation? read
      pure (evalPlainBinary op leftOutcome rightOutcome)
  | .power _ _ | .round _ _ _ => none

/-- Evaluate a raw core. The unknown fallback fails closed for a forged unsupported core and is unreachable through the checked route. -/
def NumericFixedRightComparison.evalSelected
    (comparison : NumericFixedRightComparison) (context : FlatContext) : Verdict :=
  match comparison.left.lowerForEvaluation.evalPlainValidation?
      context.resolveNumericArithmetic with
  | some outcome => comparison.op.evalArithmeticFixedRight outcome comparison.right.value
  | none => .unknown

/-- Evaluate one already row-selected checked comparison. -/
def CheckedNumericFixedRightComparison.evalSelected
    (checked : CheckedNumericFixedRightComparison model)
    (context : FlatContext) : Verdict :=
  checked.core.evalSelected context

/-- A plain comparison never fires on an entirely blank full-validation row. -/
def CheckedNumericFixedRightComparison.evalFull
    (checked : CheckedNumericFixedRightComparison model)
    (context : FlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then checked.evalSelected context else .notFired

/-- Check a surface comparison and evaluate it against model-derived cells under full validation. -/
def elaborateAndEvalNumericFixedRight (model : FlatModel) (rowGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool)
    (surface : SurfaceNumericFixedRightComparison) :
    Except NumericValidationElabError Verdict := do
  let checked ← elaborateNumericFixedRight model rowGroup surface
  pure (checked.evalFull (model.checkContext raw) hasContent)

end A12Kernel
