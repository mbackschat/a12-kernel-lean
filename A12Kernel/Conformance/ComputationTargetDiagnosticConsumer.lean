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

private def repeatedConfirm : FlatFieldDecl := {
  id := 34
  groupPath := ["Root", "Rows"]
  name := "RepeatedConfirm"
  policy := { kind := .confirm }
  repeatableScope := [10]
}

private def rulesMarker : FlatFieldDecl := {
  id := 33
  groupPath := ["Rules"]
  name := "Marker"
  policy := { kind := .number { scale := 0, signed := false } }
}

private def consumerModel : FlatModel :=
  { model with fields :=
      booleanTarget :: confirmTarget :: repeatedConfirm :: rulesMarker ::
        stringTarget :: model.fields }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberDecision
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :
    ComputationTargetDiagnosticDecision :=
  decideNumberTargetDiagnostic
    (elaborateNumericComputationOperation model ["Root"] targetId expression
      suppressExactScaleWarning)

/-- A scale-2 Number beside the scale-0 target, so a self-read's scale gate can fail. -/
private def fractionModel : FlatModel :=
  { model with fields := model.fields ++
      [{ numberDeclaration 35 "Frac" with policy := { kind := .number { scale := 2, signed := true } } }] }

private def fractionDecision (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    ComputationTargetDiagnosticDecision :=
  decideNumberTargetDiagnostic
    (elaborateNumericComputationOperation fractionModel ["Root"] targetId expression)

private def stringDecision (expression : StringExpr SurfaceFieldPath) :
    ComputationTargetDiagnosticDecision :=
  decideStringTargetDiagnostic
    (elaborateStringComputationOperation consumerModel ["Root"] stringTarget.id
      expression)

private def booleanConstantDecisionIn (declaringGroup : GroupPath)
    (target : FieldId) (value : Bool) :
    ComputationTargetDiagnosticDecision :=
  decideBooleanConstantTargetDiagnostic
    (checkBooleanConstantComputation consumerModel declaringGroup target value)

private def booleanConstantDecision (target : FieldId) (value : Bool) :
    ComputationTargetDiagnosticDecision :=
  booleanConstantDecisionIn ["Root"] target value

private def booleanConstantOperation?
    (target : FieldId) (value : Bool) : Option BooleanConstantOperation :=
  match checkBooleanConstantComputation consumerModel ["Root"] target value with
  | .ok checked => some checked.operation.operation
  | .error _ => none

/- The measured constant/target combinations preserve the Confirm asymmetry and each exact refusal
   code. The wrong-kind target is **not** a local unsupported refusal: it carries a Kernel class of
   its own, and which one depends on the kind
   ([checkpoint](../../docs/SOURCES.md#src-boolean-constant-target-kind-partitions-into-four-classes)).
   A String target draws neither the Confirm code nor a shared "wrong type" code, which is the
   distinction a single-code account would erase. -/
example :
    booleanConstantDecision booleanTarget.id true = .accepted ∧
      booleanConstantDecision booleanTarget.id false = .accepted ∧
      booleanConstantDecision confirmTarget.id true = .accepted ∧
      booleanConstantDecision confirmTarget.id false =
        .kernelRejected .invalidCompareToYes ∧
      (booleanConstantDecision confirmTarget.id false).kernelCode? =
        some "MVK_INVALID_COMPARE_TO_YES" ∧
      booleanConstantDecision stringTarget.id true =
        .kernelRejected .invalidCompareToEnumOrString ∧
      (booleanConstantDecision stringTarget.id true).kernelCode? =
        some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING" := by
  native_decide

/- The partition itself, over every kind the gate can receive. Four classes rather than one: the
   three temporal families share theirs, String and Enumeration share another, and Number and
   DATE_RANGE each have their own. Boolean and Confirm are absent because both are admitted targets,
   which is what makes this arm's `none` a statement rather than a gap. -/
example :
    ([SurfaceScalarKind.string, .enumeration, .number, .temporal .date,
      .temporal .time, .temporal .dateTime, .dateRange].map
        fun kind =>
          (BooleanConstantOperationElabError.targetKind kind).diagnostic?) =
      [some .invalidCompareToEnumOrString, some .invalidCompareToEnumOrString,
        some .inconsistentTypesCompared, some .invalidCompareToDate,
        some .invalidCompareToDate, some .invalidCompareToDate,
        some .invalidCompareToDateRange] := by
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

/- Target resolution and fixed placement remain distinct local refusals with no claimed Kernel code. A different valid fixed declaration group is accepted because target placement owns execution scope. -/
example :
    let invalidGroup := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel [] booleanTarget.id true)
    let malformedGroup := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Rules", ""]
        booleanTarget.id true)
    let unknown := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Root"] 999 true)
    let crossGroup := booleanConstantDecisionIn ["Rules"]
      booleanTarget.id true
    let repeatable := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Root", "Rows"]
        repeated.id true)
    invalidGroup = .booleanConstantRefusal
        (.target (.invalidRuleGroup [])) ∧
      malformedGroup = .booleanConstantRefusal
        (.target (.invalidRuleGroup ["Rules", ""])) ∧
      unknown = .booleanConstantRefusal (.target (.unknownFieldId 999)) ∧
      crossGroup = .accepted ∧
      repeatable = .booleanConstantRefusal
        (.targetRepeatable repeated.path) ∧
      invalidGroup.kernelCode? = none ∧
      malformedGroup.kernelCode? = none ∧
      unknown.kernelCode? = none ∧
      crossGroup.kernelCode? = none ∧
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

/- A Number operation reading its own target draws the reference class whatever its shape, a bare
copy, a wrapper, an operand-list call, a rounded division, a power, and both sides at once, which the
Kernel reports once per occurrence. The class is asked after the authoring and scale gates on every
shape, so a mismatched scale draws the scale class, and too many divisions or a power over a power
draw their own class, as each does beside a control without the self-read
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)). -/
example :
    let selfRead := surfaceField ["Root"] "Target"
    let frac := surfaceField ["Root"] "Frac"
    let other := surfaceField ["Root"] "Source"
    [AuthoredNumericExpr.abs selfRead, selfRead,
        .extremumCall .maximum (.extremum .maximum selfRead other),
        .round .halfUp ⟨0, by decide⟩ (.binary .divide selfRead (.literal { value := 2, authoredScale := 0 })),
        .power selfRead (.literal { value := 2, authoredScale := 0 }), .binary .add selfRead selfRead].map
          (fun expression => (fractionDecision expression).kernelCode?) =
      List.replicate 6 (some "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD") ∧
    [.extremumCall .maximum (.extremum .maximum selfRead frac),
        .binary .multiply (.abs selfRead) frac, .abs (.binary .multiply selfRead frac),
        .binary .divide selfRead other, .binary .multiply (.binary .multiply selfRead selfRead) frac,
        .binary .multiply selfRead (.literal { value := 3 / 2, authoredScale := 1 })].map
          (fun expression => (fractionDecision expression).kernelCode?) =
      List.replicate 6 (some "MVK_INVALID_COMPARE_DEC_PLACES") ∧
    (fractionDecision (.binary .divide (.binary .divide selfRead other)
        (surfaceField ["Root"] "Later"))).kernelCode? = some "MVK_TOO_MANY_DIV_FOR_CALC" ∧
    [selfRead, other].map (fun base =>
        (fractionDecision (.power (.power base (.literal { value := 2, authoredScale := 0 }))
          (.literal { value := 2, authoredScale := 0 }))).kernelCode?) =
      List.replicate 2 (some "MVK_TOO_MANY_POW_FOR_CALC") ∧
    [surfaceAggregate .sum "Target" ["Source"], surfaceAggregate .sum "Target" ["Frac"],
        .binary .multiply (surfaceAggregate .sum "Target" ["Source"]) frac,
        surfaceAggregate .sum "Source" ["Later"]].map (fun expression =>
          (fractionDecision expression).kernelCode?) =
      [some "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", some "MVK_INVALID_COMPARE_DEC_PLACES",
        some "MVK_INVALID_COMPARE_DEC_PLACES", none] ∧
    fractionDecision (surfaceAggregate .sum "Source" ["Later"]) = .accepted := by
  native_decide

/- Explain keeps an unmeasured String refusal, a range that starts at zero, as its exact local
refusal. Its missing external code is distinct from an accepted operation. -/
example :
    let uncoveredString : StringExpr SurfaceFieldPath := .range (bare "Wrong") 0 1
    let acceptedString : StringExpr SurfaceFieldPath := .field (bare "Wrong")
    stringDecision uncoveredString = .stringRefusal (.invalidRange 0 1) ∧
      stringDecision acceptedString = .accepted ∧
      (stringDecision uncoveredString).kernelCode? = none ∧
      (stringDecision acceptedString).kernelCode? = none := by
  native_decide

/- Every measured String target read translates to the shared external class, a concatenation
around the read included. -/
example :
    [StringExpr.field (bare "StringTarget"), .range (bare "StringTarget") 1 1,
        .concat (.field (bare "StringTarget")) (.literal "X")].map stringDecision =
      List.replicate 3 (.kernelRejected .errorReferenceToCalculatedField) ∧
      (stringDecision (.field (bare "StringTarget"))).kernelCode? =
        some "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD" := by
  native_decide

/- Fixed placement is checked before the constant, so a repeatable Confirm target reports the local
placement refusal and no Kernel code at all. The Confirm asymmetry two examples above holds only once
the target is fixed; reading the two gates in their documented listing order instead reports
`MVK_INVALID_COMPARE_TO_YES` here and loses the placement cause. -/
example :
    let repeatableConfirmFalse := decideBooleanConstantTargetDiagnostic
      (checkBooleanConstantComputation consumerModel ["Root"]
        repeatedConfirm.id false)
    repeatableConfirmFalse = .booleanConstantRefusal
        (.targetRepeatable repeatedConfirm.path) ∧
      repeatableConfirmFalse.kernelCode? = none := by
  native_decide

end A12Kernel.Conformance.ComputationTargetDiagnosticConsumer
