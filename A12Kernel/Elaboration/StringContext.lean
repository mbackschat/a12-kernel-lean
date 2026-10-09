import A12Kernel.Elaboration.CustomField
import A12Kernel.Elaboration.StringPattern

/-! # A12Kernel.Elaboration.StringContext — shared prepared flat String context

Ordinary declared patterns and registered custom validators are mutually exclusive declaration profiles, but both refine the same raw-to-checked String read. This module prepares both model-complete capability sets after one model-validation pass and composes their existing checkers without adding another String classifier.
-/

namespace A12Kernel

/-- Compile the closed ASCII profiles without a host regex capability. -/
def builtinStringPatternCompiler : StringPatternCompiler :=
  locallyExecutableStringPatternMatcher?

inductive FlatStringContextPreparationError where
  | model (error : ResolveError)
  | pattern (error : DeclaredStringPatternElabError)
  | custom (error : CustomFieldTypeElabError)
  deriving Repr, DecidableEq

inductive FlatStringContextEvaluationError where
  | preparation (error : FlatStringContextPreparationError)
  | condition (error : ElabError)
  deriving Repr, DecidableEq

/-- The two mutually exclusive prepared String capabilities for one validated flat model. -/
structure PreparedFlatStringContext (model : FlatModel)
    (compilePattern : StringPatternCompiler) where
  world : World
  patterns : PreparedFlatStringPatterns model compilePattern
  customFields : PreparedFlatCustomFields model

namespace PreparedFlatStringContext

/-- Registered custom checking owns custom declarations; every other declaration falls through to the model-complete ordinary-pattern context. -/
def checkContext
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) : FlatContext :=
  prepared.customFields.checkContextOver locale
    (prepared.patterns.checkContext raw) raw

end PreparedFlatStringContext

/-- Validate once, then prepare every ordinary declared matcher and registered custom validator against that exact model. -/
def prepareFlatStringContext (world : World)
    (compilePattern : StringPatternCompiler) (model : FlatModel) :
    Except FlatStringContextPreparationError
      (PreparedFlatStringContext model compilePattern) :=
  match hModel : model.validate with
  | .error error => .error (.model error)
  | .ok () =>
      match prepareDeclaredStringPatterns compilePattern model.fields with
      | .error error => .error (.pattern error)
      | .ok patterns =>
          match prepareCustomDeclarations world model.fields with
          | .error error => .error (.custom error)
          | .ok customFields =>
              let modelWellFormed : model.validate.isOk = true := by
                rw [hModel]
                rfl
              .ok {
                world
                patterns := { fields := patterns, modelWellFormed }
                customFields := { fields := customFields }
              }

/-- Prepare both String capability families, elaborate against the same model, and evaluate through their one shared checked context. -/
def elaborateAndEvalFull
    (compilePattern : StringPatternCompiler) (locale : String)
    (model : FlatModel) (world : World) (declaringGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool)
    (condition : SurfaceCondition) :
    Except FlatStringContextEvaluationError Verdict := do
  let prepared ←
    (prepareFlatStringContext world compilePattern model).mapError .preparation
  let checked ←
    (elaborate model declaringGroup condition).mapError .condition
  pure (checked.core.evalFull
    ((prepared.checkContext locale raw).withWorld world) hasContent)

/-- Apply the full-validation row gate, then use the model-complete prepared String context. Pattern leaves cannot fire on an all-empty row. -/
def CheckedStringPatternCondition.evalFull (checked : CheckedStringPatternCondition model compilePattern)
    (prepared : PreparedFlatStringContext model compilePattern)
    (raw : RawFlatContext) (hasContent : Bool) (locale : String := "en_US") : Verdict :=
  if hasContent then
    checked.evalSelected (prepared.checkContext locale raw)
  else
    .notFired

inductive PreparedStringPatternEvaluationError where
  | preparation (error : FlatStringContextPreparationError)
  | condition (error : StringPatternConditionElabError)
  deriving Repr, DecidableEq

/-- Prepare every declared field pattern, elaborate the authored pattern leaf against the same model, and evaluate through that complete checked context. -/
def elaborateAndEvalStringPatternFull
    (compilePattern : StringPatternCompiler) (model : FlatModel)
    (rowGroup : GroupPath) (raw : RawFlatContext) (hasContent : Bool)
    (surface : SurfaceStringPatternCondition) (world : World := { now := { epochMillis := 0 } })
    (locale : String := "en_US") :
    Except PreparedStringPatternEvaluationError Verdict := do
  let prepared ←
    (prepareFlatStringContext world compilePattern model).mapError .preparation
  let checked ←
    (elaborateStringPatternCondition compilePattern model rowGroup surface)
      |>.mapError .condition
  pure (checked.evalFull prepared raw hasContent locale)

end A12Kernel
