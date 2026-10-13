import A12Kernel.Elaboration.DeclarationReport
import A12Kernel.Elaboration.ErrorTargetDeclaration
import A12Kernel.Elaboration.ConditionDiagnostic
import A12Kernel.Elaboration.ValidationMessageDiagnostic
import A12Kernel.Conformance.ValidationMessageAuthoring

/-! # One declaration's report against the Kernel's model check

Every expected list is the code list of one row of the
[declaration-report capture](../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14),
compared as a multiset because the Kernel interleaves members. The rule sits in `/Form`, targets
`Value` and reads `Value` unless the row says otherwise, under the code `CODE` with one English text.
The condition's class and the template's classes come from their own checkers, so each row also
exercises the producer feeding the report. -/

namespace A12Kernel.Conformance.DeclarationReport

open A12Kernel
open A12Kernel.Conformance.ValidationMessageAuthoring (keywordProfile)

private def str (id : Nat) (name : String) : FlatFieldDecl :=
  { id, groupPath := ["Form"], name, policy := { kind := .string } }

private def model : FlatModel := { fields := [str 0 "Value", str 1 "Other"] }

private def bare (field : String) : SurfaceFieldPath := { base := .relative 0, groups := [], field }

private def readsValue : SurfaceCondition := .fieldFilled (bare "Value")

/-- The condition checker's class, `none` for an admitted condition. -/
private def conditionClass (condition : SurfaceCondition) : Option KernelStaticDiagnostic :=
  match elaborate model ["Form"] condition with
  | .error error => condition.refusalDiagnostic? error
  | .ok _ => none

/-- The template checker's classes beside the sound condition reading `Value`. -/
private def templateClasses (text : String) : List KernelStaticDiagnostic :=
  match elaborate model ["Form"] readsValue with
  | .error _ => []
  | .ok condition =>
      (validationMessageTemplateRefusals model keywordProfile condition text).filterMap
        (·.namedRuleDiagnostic?)

private def tab : String := "a\tb"

private def rule (name : String := "Probe") (code : String := "CODE")
    (target : ErrorFieldDeclaration := .declared true) (condition : SurfaceCondition := readsValue)
    (relational : List KernelStaticDiagnostic := []) (locales : List String := ["en_US"])
    (entries : List (String × String) := [("en_US", "plain text")]) : List String :=
  let declaration : ExecutableDeclaration := { group := ["Form"], name, kind := .rule (.text code) }
  let verdicts : DeclarationVerdicts := {
    slots := declaration.notifications.filterMap (·.kind.diagnostic?)
    target := targetClasses false target
    firstRaised := conditionClass condition
    relational
    presence := messagePresence locales entries
    errorText := errorTextClasses locales entries templateClasses }
  (verdicts.report.map (·.kernelCode)).mergeSort (compare · · != .gt)

private def kernel (codes : List String) : List String := codes.mergeSort (compare · · != .gt)

private def unknownName : SurfaceCondition := .fieldFilled (bare "Nope")

/- A failed target ends the rule: the condition's and the template's classes are withheld, while the
   name, code and prefixed presence classes stand beside the pair. A union of member verdicts adds the
   entity class to the second row and the character class to the third. -/
example :
    rule (target := .absent) = kernel ["MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"] ∧
    rule (target := .absent) (condition := unknownName) =
      kernel ["MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"] ∧
    rule (target := .absent) (entries := [("en_US", tab)]) =
      kernel ["MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"] ∧
    rule (target := .absent) (name := "vk_vkProbe") =
      kernel ["MVK_ERROR_FIELD_MISSING", "MVK_RULE_NAME_INVALID", "MVK_MISSING_ERROR_FIELD"] ∧
    rule (target := .absent) (code := " ") =
      kernel ["MVK_ERROR_CODE_MISSING", "MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"] ∧
    rule (target := .absent) (entries := []) =
      kernel ["MVK_ERROR_MESSAGE_MISSING", "MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"] ∧
    rule (target := .absent) (entries := [("en_US", "   ")]) =
      kernel ["MVK_ERROR_MESSAGE_MISSING", "MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"] := by
  native_decide

/- A refused condition withholds the error-text checker, the unprefixed missing-text class included,
   and not the other slots. The last row is the twin: without the refusal the character class stands. -/
example :
    rule (condition := unknownName) (entries := [("en_US", tab)]) = kernel ["MVK_INVALID_ENTITY"] ∧
    rule (condition := unknownName) (entries := []) =
      kernel ["MVK_ERROR_MESSAGE_MISSING", "MVK_INVALID_ENTITY"] ∧
    rule (condition := unknownName) (name := "vk_vkProbe") (code := " ") (entries := [("en_US", tab)]) =
      kernel ["MVK_ERROR_CODE_MISSING", "MVK_RULE_NAME_INVALID", "MVK_INVALID_ENTITY"] ∧
    rule (name := "vk_vkProbe") (code := " ") (entries := [("en_US", tab)]) =
      kernel ["MVK_ERROR_CODE_MISSING", "MVK_RULE_NAME_INVALID", "INVALID_CHARACTERS"] := by
  native_decide

/- The relational class withholds the error text like any refusal, and gives way to a positioned
   class. Its producer is the target cascade, so these rows supply it. -/
example :
    rule (condition := .fieldFilled (bare "Other")) (relational := [.errorFieldNotReferenced])
        (entries := [("en_US", tab)]) = kernel ["MVK_ERROR_FIELD_NOT_REFERENCED"] ∧
    rule (condition := .fieldFilled (bare "Other")) (relational := [.errorFieldNotReferenced])
        (entries := []) = kernel ["MVK_ERROR_MESSAGE_MISSING", "MVK_ERROR_FIELD_NOT_REFERENCED"] ∧
    rule (condition := .and (.fieldFilled (bare "Other")) unknownName)
        (relational := [.errorFieldNotReferenced]) = kernel ["MVK_INVALID_ENTITY"] ∧
    rule (condition := .and (.and unknownName (.fieldFilled (bare "Nope2"))) readsValue) =
      kernel ["MVK_INVALID_ENTITY"] := by
  native_decide

/- Every slot reports, and the missing-text pair splits over the declared locales: a blank text
   answers no locale and still counts as written, so it draws the prefixed class alone. -/
example :
    rule (entries := []) = kernel ["MVK_ERROR_MESSAGE_MISSING", "RULE_HAS_NO_ERRORTEXT"] ∧
    rule (entries := [("en_US", "   ")]) = kernel ["MVK_ERROR_MESSAGE_MISSING"] ∧
    rule (entries := [("en_US", "")]) = kernel ["MVK_ERROR_MESSAGE_MISSING", "RULE_HAS_NO_ERRORTEXT"] ∧
    rule (name := "vk_vkProbe") (code := " ") (entries := []) =
      kernel ["MVK_ERROR_CODE_MISSING", "MVK_ERROR_MESSAGE_MISSING", "MVK_RULE_NAME_INVALID",
        "RULE_HAS_NO_ERRORTEXT"] := by
  native_decide

private def twoLocales : List String := ["en_US", "de_DE"]

example :
    rule (locales := twoLocales) (entries := [("en_US", "  "), ("de_DE", "  ")]) =
      kernel ["MVK_ERROR_MESSAGE_MISSING"] ∧
    rule (locales := twoLocales) (entries := [("en_US", "x"), ("de_DE", "")]) =
      kernel ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING", "RULE_HAS_NO_ERRORTEXT"] ∧
    rule (locales := twoLocales) (entries := [("en_US", "x"), ("de_DE", " ")]) =
      kernel ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING"] ∧
    rule (locales := twoLocales) (entries := [("en_US", "x")]) =
      kernel ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING", "RULE_HAS_NO_ERRORTEXT"] ∧
    rule (locales := twoLocales) (entries := [("en_US", ""), ("de_DE", " ")]) =
      kernel ["MVK_ERROR_MESSAGE_MISSING", "RULE_HAS_NO_ERRORTEXT"] ∧
    rule (locales := twoLocales) (condition := unknownName) (entries := [("en_US", "x")]) =
      kernel ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING", "MVK_INVALID_ENTITY"] := by
  native_decide

/- Each failing parameter reports unless the character gate stops the text, and each declared
   locale's text is asked on its own. -/
example :
    rule (entries := [("en_US", "see $Nope$ and $Other$")]) = kernel ["INVALID_ENTITY", "INVALID_FIELD"] ∧
    rule (entries := [("en_US", "see $Nope$ a\tb")]) = kernel ["INVALID_CHARACTERS"] ∧
    rule (locales := twoLocales) (entries := [("en_US", tab), ("de_DE", "see $Other$")]) =
      kernel ["INVALID_CHARACTERS", "INVALID_FIELD"] := by
  native_decide

/- A computation has no target and no error code; its operation's class withholds its template. -/
example :
    let computation (firstRaised : Option KernelStaticDiagnostic) (entries : List (String × String)) :=
      kernel (({ slots := [], firstRaised
                 presence := messagePresence ["en_US"] entries
                 errorText := errorTextClasses ["en_US"] entries templateClasses } :
                DeclarationVerdicts).report.map (·.kernelCode))
    computation (some .invalidEntity) [] = kernel ["MVK_INVALID_ENTITY", "MVK_ERROR_MESSAGE_MISSING"] ∧
    computation (some .invalidEntity) [("en_US", tab)] = kernel ["MVK_INVALID_ENTITY"] := by
  native_decide

end A12Kernel.Conformance.DeclarationReport
