import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Validate

/-! # The suppression pragma of a computation or rule

A computation's `errorCodesToSuppress` is rendered as one `@SuppressWarning(…)` pragma of the model's
condition language, so its class is the pragma's: one entry that lexes as a single name is admitted
when it is the scale warning and refused with `MVK_INVALID_SUPPRESSED_WARNING` otherwise, and two
entries fail the parse (spec/12 §4). The rows `sw-1`, `sw-twin` and `sw-two` replay the retained
Kernel 30.8.1 capture `evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/`;
the lower-case and padded names are statements of spec/12 §4 without a retained row of their own.

The rule route shares the pragma gate and is locked once, since a rule carries the pragma as text.
-/

namespace A12Kernel.Dm.SuppressionPragmaLocks

open A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Total", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, name := "Ref", groupPath := ["Form"], policy := { kind := .string } }] }

/-- The code a computation declaring these suppressed entries is refused on, or `admitted`. -/
private def computationOutcome (suppressed : List String) : String :=
  match lowerComputation model .english {
    group := ["Form"], name := "Cp", targetRelPath := "../Total", commonPrecondition := none
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := suppressed } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

private def ruleOutcome (name : String) : String :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkRule dm .english {
    group := ["Form"], name := "R", errorEntityRelPath := "../Ref", errorCode := "E", severity := "ERROR"
    condition := s!"@SuppressWarning({name}) FieldFilled(Ref)" } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

private def scaleWarning : String := "MVK_INVALID_COMPARE_DEC_PLACES"

example : KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode = "MVK_INVALID_SUPPRESSED_WARNING" := rfl

-- sw-1 (an unknown name), sw-twin (the scale warning) and sw-two (two entries).
example :
    computationOutcome ["MVK_BOGUS"] == KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode &&
    computationOutcome [scaleWarning] == "admitted" &&
    computationOutcome [scaleWarning, scaleWarning] == KernelStaticDiagnostic.unexpectedToken.kernelCode := by
  native_decide

-- A genuine code the Kernel does not let a pragma suppress is refused like an invented one, and the name
-- is compared case-sensitively; whitespace around it is not part of the name.
example :
    computationOutcome ["MVK_NO_NUMBER"] == KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode &&
    computationOutcome [scaleWarning.toLower] == KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode &&
    computationOutcome [s!"  {scaleWarning}  "] == "admitted" &&
    computationOutcome [s!"\t\n{scaleWarning}"] == "admitted" := by
  native_decide

-- A list led by an unsupported name fails the parse ahead of the name gate (spec/12 §4).
example : computationOutcome ["MVK_BOGUS", scaleWarning] == KernelStaticDiagnostic.unexpectedToken.kernelCode := by
  native_decide

-- The rule route reports the same class for the same name.
example :
    ruleOutcome "MVK_BOGUS" == KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode &&
    ruleOutcome scaleWarning == "admitted" := by
  native_decide

end A12Kernel.Dm.SuppressionPragmaLocks
