import A12Kernel.Conformance.NumericComputation.Support
import A12Kernel.Elaboration.BooleanConstantComputation
import A12Kernel.Elaboration.StringComputation

/-! # Computed-target diagnostic Translate/Explain probe

This bounded consumer probe uses the existing Boolean-constant, Number, and String elaboration results and per-family diagnostic projections. Translate receives an exact Kernel code only for established mappings. Explain retains an unmapped local refusal instead of collapsing it into acceptance or inventing an external class.
-/

namespace A12Kernel.Conformance.ComputationTargetDiagnosticConsumer

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private inductive ComputationTargetDiagnosticDecision where
  | accepted
  | kernelRejected (diagnostic : KernelStaticDiagnostic)
  | booleanConstantRefusal (error : BooleanConstantComputationElabError)
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

private def decideBooleanConstantTargetDiagnostic {α} :
    Except BooleanConstantComputationElabError α →
      ComputationTargetDiagnosticDecision
  | .ok _ => .accepted
  | .error error =>
      match error.diagnostic? with
      | some diagnostic => .kernelRejected diagnostic
      | none => .booleanConstantRefusal error

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

private def booleanTarget : FlatFieldDecl := {
  id := 31
  groupPath := ["Root"]
  name := "BooleanTarget"
  policy := { kind := .boolean }
}

private def confirmTarget : FlatFieldDecl := {
  id := 32
  groupPath := ["Root"]
  name := "ConfirmTarget"
  policy := { kind := .confirm }
}

private def consumerModel : FlatModel :=
  { model with fields :=
      booleanTarget :: confirmTarget :: stringTarget :: model.fields }

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

private def booleanConstantDecision (target : FieldId) (value : Bool) :
    ComputationTargetDiagnosticDecision :=
  decideBooleanConstantTargetDiagnostic
    (checkBooleanConstantComputation consumerModel ["Root"] target value)

private def booleanConstantOperation?
    (target : FieldId) (value : Bool) : Option BooleanConstantOperation :=
  match checkBooleanConstantComputation consumerModel ["Root"] target value with
  | .ok checked => some checked.operation.operation
  | .error _ => none

/- The four measured constant/target combinations preserve the Confirm asymmetry and exact refusal code. A non-Boolean target remains a local unsupported refusal rather than being mistaken for acceptance or assigned an unmeasured Kernel class. -/
example :
    booleanConstantDecision booleanTarget.id true = .accepted ∧
      booleanConstantDecision booleanTarget.id false = .accepted ∧
      booleanConstantDecision confirmTarget.id true = .accepted ∧
      booleanConstantDecision confirmTarget.id false =
        .kernelRejected .invalidCompareToYes ∧
      (booleanConstantDecision confirmTarget.id false).kernelCode? =
        some "MVK_INVALID_COMPARE_TO_YES" ∧
      booleanConstantDecision stringTarget.id true =
        .booleanConstantRefusal
          (.operation stringTarget.path (.targetKind .string)) ∧
      (booleanConstantDecision stringTarget.id true).kernelCode? = none := by
  native_decide

/- Acceptance retains the authored Boolean payload and the distinct Confirm constructor instead of erasing both successful routes to one undifferentiated constant. -/
example :
    booleanConstantOperation? booleanTarget.id true =
        some (.boolean true) ∧
      booleanConstantOperation? booleanTarget.id false =
        some (.boolean false) ∧
      booleanConstantOperation? confirmTarget.id true =
        some .confirmTrue := by
  native_decide

/- Target resolution, declaring-group ownership, and fixed placement remain distinct local refusals with no claimed Kernel code. -/
example :
    let unknown := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Root"] 999 true)
    let wrongGroup := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Other"]
        booleanTarget.id true)
    let repeatable := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Root", "Rows"]
        repeated.id true)
    unknown = .booleanConstantRefusal (.target (.unknownFieldId 999)) ∧
      wrongGroup = .booleanConstantRefusal
        (.targetGroup ["Root"] ["Other"]) ∧
      repeatable = .booleanConstantRefusal
        (.targetRepeatable repeated.path) ∧
      unknown.kernelCode? = none ∧
      wrongGroup.kernelCode? = none ∧
      repeatable.kernelCode? = none := by
  native_decide

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
