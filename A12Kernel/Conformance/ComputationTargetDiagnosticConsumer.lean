import A12Kernel.Conformance.NumericComputation.Support
import A12Kernel.Elaboration.StringComputation

/-! # Computed-target diagnostic Translate/Explain probe

This bounded consumer probe uses the existing Number and String elaboration results and per-family diagnostic projections. Translate receives an exact Kernel code only for established mappings. Explain retains an unmapped local refusal instead of collapsing it into acceptance or inventing an external class.
-/

namespace A12Kernel.Conformance.ComputationTargetDiagnosticConsumer

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private inductive ComputationTargetDiagnosticDecision where
  | accepted
  | kernelRejected (diagnostic : KernelStaticDiagnostic)
  | numberRefusal (error : NumericComputationElabError)
  | stringRefusal (error : StringComputationElabError)
  deriving Repr, DecidableEq

private def ComputationTargetDiagnosticDecision.kernelCode? :
    ComputationTargetDiagnosticDecision → Option String
  | .kernelRejected diagnostic => some diagnostic.kernelCode
  | _ => none

private def decideNumberTargetDiagnostic {α} :
    Except NumericComputationElabError α →
      ComputationTargetDiagnosticDecision
  | .ok _ => .accepted
  | .error error =>
      match error.targetDiagnostic? with
      | some diagnostic => .kernelRejected diagnostic
      | none => .numberRefusal error

private def decideStringTargetDiagnostic {α} :
    Except StringComputationElabError α →
      ComputationTargetDiagnosticDecision
  | .ok _ => .accepted
  | .error error =>
      match error.targetDiagnostic? with
      | some diagnostic => .kernelRejected diagnostic
      | none => .stringRefusal error

private def stringTarget : FlatFieldDecl :=
  stringDeclaration 30 "StringTarget"

private def consumerModel : FlatModel :=
  { model with fields := stringTarget :: model.fields }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberDecision
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :
    ComputationTargetDiagnosticDecision :=
  decideNumberTargetDiagnostic
    (elaborateNumericComputationOperation model ["Root"] targetId expression
      suppressExactScaleWarning)

private def stringDecision (expression : StringExpr SurfaceFieldPath) :
    ComputationTargetDiagnosticDecision :=
  decideStringTargetDiagnostic
    (elaborateStringComputationOperation consumerModel ["Root"] stringTarget.id
      expression)

/- Translate preserves scale versus self-reference identity, and suppression
reveals the reached self-reference rather than manufacturing acceptance. -/
example :
    let targetField := surfaceField ["Root"] "Target"
    let sourceField := surfaceField ["Root"] "Source"
    let scaleOne : AuthoredNumericExpr SurfaceNumericAtom :=
      .literal { value := 3 / 2, authoredScale := 1 }
    let scaleZero : AuthoredNumericExpr SurfaceNumericAtom :=
      .literal { value := 2, authoredScale := 0 }
    let mismatched := AuthoredNumericExpr.binary .multiply targetField scaleOne
    let accepted := AuthoredNumericExpr.binary .multiply sourceField scaleZero
    numberDecision mismatched = .kernelRejected .invalidCompareDecimalPlaces ∧
      numberDecision mismatched true =
        .kernelRejected .errorReferenceToCalculatedField ∧
      numberDecision accepted = .accepted ∧
      (numberDecision mismatched).kernelCode? =
        some "MVK_INVALID_COMPARE_DEC_PLACES" ∧
      (numberDecision mismatched true).kernelCode? =
        some "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD" := by
  native_decide

/- Explain keeps uncovered Number and String target reads as their exact local
refusals. Their missing external code is distinct from an accepted operation. -/
example :
    let numberTarget := surfaceField ["Root"] "Target"
    let uncoveredNumber := AuthoredNumericExpr.abs numberTarget
    let uncoveredString : StringExpr SurfaceFieldPath :=
      .concat (.field (bare "StringTarget")) (.literal "X")
    let acceptedString : StringExpr SurfaceFieldPath := .field (bare "Wrong")
    numberDecision uncoveredNumber =
        .numberRefusal (.targetSelfReference targetId) ∧
      stringDecision uncoveredString =
        .stringRefusal (.targetSelfReference stringTarget.id) ∧
      stringDecision acceptedString = .accepted ∧
      (numberDecision uncoveredNumber).kernelCode? = none ∧
      (stringDecision uncoveredString).kernelCode? = none ∧
      (stringDecision acceptedString).kernelCode? = none := by
  native_decide

/- Both measured String root forms translate to the shared external class. -/
example :
    stringDecision (.field (bare "StringTarget")) =
        .kernelRejected .errorReferenceToCalculatedField ∧
      stringDecision (.range (bare "StringTarget") 1 1) =
        .kernelRejected .errorReferenceToCalculatedField ∧
      (stringDecision (.field (bare "StringTarget"))).kernelCode? =
        some "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD" := by
  native_decide

end A12Kernel.Conformance.ComputationTargetDiagnosticConsumer
