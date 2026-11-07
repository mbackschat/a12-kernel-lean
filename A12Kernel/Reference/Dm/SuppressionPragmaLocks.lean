import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.ComputationCheck

/-! # The suppression pragma of a computation or rule

A computation's preamble is its `additionalParserInformation` text unless blank, else its legacy
`errorCodesToSuppress` folded into one `@SuppressWarning(…)` pragma of the model's condition language; kernel
31.3.1 parses it alone and first, so its class is the computation's only one (a12-dmkits KF298 re-measured
2026-11-07, [inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §5). The pragma
takes a comma list of names, each the scale warning or the Enumeration calculation class; one entry's lexical
and token classes are the 30.8.1 rows `sw-1` and `sw-twin` of
`evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/` and spec/12 §4's single-entry
table, whose shape the 31.3.1 grammar keeps.

The rule route shares the pragma gate and is locked once, since a rule carries the pragma as text; it
is the admission entry `checkValidationRule`, whose syntax refusals take the first class a production
raised (spec/12 §3.1).
-/

namespace A12Kernel.Dm.SuppressionPragmaLocks

open A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Total", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, name := "Ref", groupPath := ["Form"], policy := { kind := .string } }] }

/-- The code a computation declaring these legacy entries, and optionally a parser-information text, is
refused on, or `admitted`. -/
private def computationOutcome (suppressed : List String) (text : Option String := none) : String :=
  match lowerComputation model .english {
    group := ["Form"], name := "Cp", targetRelPath := "../Total", commonPrecondition := none
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := suppressed
    parserInformation := text } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

private def ruleOutcome (name : String) : String :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkValidationRule dm .english {
    group := ["Form"], name := "R", errorEntityRelPath := "../Ref", errorCode := "E", severity := "ERROR"
    condition := s!"@SuppressWarning({name}) FieldFilled(Ref)" } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

private def scaleWarning : String := "MVK_INVALID_COMPARE_DEC_PLACES"

example : KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode = "MVK_INVALID_SUPPRESSED_WARNING" := rfl

private def unexpected : String := KernelStaticDiagnostic.unexpectedToken.kernelCode
private def unsupported : String := KernelStaticDiagnostic.invalidSuppressedWarning.kernelCode
private def enumCalculation : String := "MVK_ERROR_INVALID_ENUM_CALCULATION"

-- sw-1 (an unknown name) and sw-twin (the scale warning); a list of supported names, repeated or padded, is
-- admitted, and an unsupported name anywhere in it is the whitelist class.
example :
    computationOutcome ["MVK_BOGUS"] == unsupported &&
    computationOutcome [scaleWarning] == "admitted" &&
    computationOutcome [scaleWarning, scaleWarning] == "admitted" &&
    computationOutcome [scaleWarning, enumCalculation] == "admitted" &&
    computationOutcome [s!" {scaleWarning} ", s!" {enumCalculation}"] == "admitted" &&
    computationOutcome ["MVK_BOGUS", scaleWarning] == unsupported &&
    computationOutcome [scaleWarning, "MVK_BOGUS"] == unsupported := by
  native_decide

-- A genuine code the Kernel does not let a pragma suppress is refused like an invented one, and the name
-- is compared case-sensitively; whitespace around it is not part of the name.
example :
    computationOutcome ["MVK_NO_NUMBER"] == unsupported &&
    computationOutcome [scaleWarning.toLower] == unsupported &&
    computationOutcome [s!"  {scaleWarning}  "] == "admitted" &&
    computationOutcome [s!"\t\n{scaleWarning}"] == "admitted" := by
  native_decide

-- An empty entry, an empty pragma, a bare code and a pragma followed by a condition are no preamble alone. A
-- numeric entry is its text, a digit-initial name.
example :
    computationOutcome ["", scaleWarning] == unexpected &&
    computationOutcome [scaleWarning, ""] == unexpected &&
    computationOutcome [] (some "@SuppressWarning()") == unexpected &&
    computationOutcome [] (some scaleWarning) == unexpected &&
    computationOutcome [] (some s!"@SuppressWarning({scaleWarning}) FieldFilled(Ref)") == unexpected &&
    computationOutcome [] (some "7") == unexpected &&
    computationOutcome ["7"] == unexpected := by
  native_decide

-- A stored text wins over the list beside it; a blank text leaves the list to answer.
example :
    computationOutcome ["MVK_BOGUS"] (some s!"@SuppressWarning({scaleWarning})") == "admitted" &&
    computationOutcome [scaleWarning] (some "@SuppressWarning(MVK_BOGUS)") == unsupported &&
    computationOutcome ["MVK_BOGUS"] (some " \t") == unsupported &&
    computationOutcome [] (some "") == "admitted" := by
  native_decide

/-- A German model folds the list into its own pragma spelling. -/
example :
    ({ group := ["Form"], name := "Cp", targetRelPath := "../Total", commonPrecondition := none
       alternatives := [], errorCodesToSuppress := ["A", "B"] } : DmComputation).preambleText .german =
      some "@UnterdrueckeWarnung(A,B)" := by
  native_decide

-- The rule route reports the same class for the same name and reads the same list grammar, which a rule's
-- own condition shares with the computation's preamble (unmeasured on a rule).
example :
    ruleOutcome "MVK_BOGUS" == unsupported &&
    ruleOutcome scaleWarning == "admitted" &&
    ruleOutcome s!"{scaleWarning}, {enumCalculation}" == "admitted" := by
  native_decide

-- A digit-initial name, a quoted name and a keyword of the model's own language lex but are no usable name at this
-- position, so they are parse failures, ahead of a later character the lexer cannot take (peer
-- KERNEL-FINDINGS' suppression table, spec/12 §4).
example :
    ruleOutcome "7_DAYS" == KernelStaticDiagnostic.unexpectedToken.kernelCode &&
    ruleOutcome "7_DAYS É" == KernelStaticDiagnostic.unexpectedToken.kernelCode &&
    ruleOutcome "'MVK_LATE'" == KernelStaticDiagnostic.unexpectedToken.kernelCode &&
    ruleOutcome "And" == KernelStaticDiagnostic.unexpectedToken.kernelCode &&
    ruleOutcome "And É" == KernelStaticDiagnostic.unexpectedToken.kernelCode := by
  native_decide

/-- The class the computation admission entry `checkComputation` reports, the entry peer KF298's rows
measure. A parser failure ahead of an unlexable character answers first; these single-entry rows are 30.8.1's,
and a second entry after the unlexable one is unmeasured since the list grammar changed. -/
private def checkedComputationOutcome (suppressed : List String) (text : Option String := none) : String :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkComputation dm .english {
    group := ["Form"], name := "Cp", targetRelPath := "../Total", commonPrecondition := none
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := suppressed
    parserInformation := text } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

example :
    checkedComputationOutcome ["7_DAYS É"] == KernelStaticDiagnostic.unexpectedToken.kernelCode &&
    checkedComputationOutcome ["And É"] == KernelStaticDiagnostic.unexpectedToken.kernelCode &&
    checkedComputationOutcome ["MVK_FRAÉ", scaleWarning] == KernelStaticDiagnostic.lexerStandardError.kernelCode &&
    checkedComputationOutcome [scaleWarning] == "admitted" := by
  native_decide

-- A preamble read alone ends where its text ends, so an unclosed one meets the end of input, while the generated
-- rule, which carries the preamble at the head of its condition, would meet the condition's first token there and
-- draw `MVK_UNEXPECTED_TOKEN`. The computation reports its alone read: the mechanism is Letter J's §5, the class
-- of an unclosed preamble derived and unmeasured.
example :
    checkedComputationOutcome [] (some "@SuppressWarning(MVK_BOGUS") ==
      KernelStaticDiagnostic.expectedTokenNotFound.kernelCode &&
    checkedComputationOutcome [] (some s!"@SuppressWarning({scaleWarning},") ==
      KernelStaticDiagnostic.expectedTokenNotFound.kernelCode &&
    checkedComputationOutcome [] (some "@SuppressWarning") ==
      KernelStaticDiagnostic.expectedTokenNotFound.kernelCode := by
  native_decide

end A12Kernel.Dm.SuppressionPragmaLocks
