import A12Kernel.Elaboration.CustomField
import A12Kernel.Elaboration.StringPattern

/-! # A12Kernel.Elaboration.StringContext — shared prepared flat String context

Ordinary declared patterns and registered custom validators are mutually exclusive declaration profiles, but both refine the same raw-to-checked String read. This module prepares both model-complete capability sets after one model-validation pass and composes their existing checkers without adding another String classifier.
-/

namespace A12Kernel

/-- The explicit compiler for the sole declared pattern whose matcher is implemented without a host regex capability. -/
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

end A12Kernel
