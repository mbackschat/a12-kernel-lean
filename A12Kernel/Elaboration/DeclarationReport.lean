import A12Kernel.Elaboration.DeclarationAdmission

/-! # Which member classes one rule or computation reports

The Kernel's model check asks a rule's or computation's members separately, and a refused member
hides some of its neighbours' classes. Measured on one model, every row a single defective
declaration ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14)):

- An error target naming nothing, or a class drawn by the DSL members, is the declaration's
  **refusal**. A target refusal ends the rule: the condition is not parsed, so its class never
  appears ([spec/07](../../spec/07-repetition-and-iteration.md)).
- A refusal withholds every class the error-text checker draws: the template's character and
  parameter classes and the unprefixed missing-text class
  ([spec/11](../../spec/11-messages-and-custom.md#part-a--13-error-message-interpolation)).
- The name and error-code classes and the two prefixed message-presence classes are other members'
  verdicts. They stand beside any refusal, the target's included.
- Within the DSL members the declaration reports **one** class. A relational class judges the
  resolved references rather than a place in the text (the error target not being referenced), and
  it stands only when no other DSL class does.

Which positioned DSL class comes first is its producer's decision, made over the declaration's
joined text; this module takes that class rather than choosing it. Each member's own multiplicity
also belongs to its checker. The template checker reports each failing parameter, and the declared
locales are each asked. The report is a multiset: the Kernel's notification order interleaves the
members, so the order here carries no claim.
-/

namespace A12Kernel

/-- The entry judged for one locale: the last one written for it. -/
private def judgedText (entries : List (String × String)) (locale : String) : Option String :=
  (entries.filter (·.1 == locale)).getLast?.map (·.2)

/-- A rule's or computation's message presence, split by the checker that draws each class. -/
structure MessagePresence where
  /-- `MVK_ERROR_MESSAGE_MISSING` or `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING`, which stand beside a
  refusal. -/
  prefixed : List KernelStaticDiagnostic := []
  /-- `RULE_HAS_NO_ERRORTEXT`, which the error-text checker draws and a refusal withholds. -/
  unprefixed : List KernelStaticDiagnostic := []
  deriving Repr, DecidableEq

/-- The presence classes for `entries`, written `(locale, text)` pairs. A locale is answered by a
nonblank judged text. The prefixed class asks whether any declared locale is answered; the
unprefixed one is drawn once for each declared locale left with no text or an empty one, so a blank
text counts as present for it and absent for the prefixed one (peer KF558; rows `m-*` of the
[sort-list supplement](../../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity)). Blankness is Java's, as for the other
declaration members (spec/01 §3); the measured blank texts are spaces. With no declared locale no
locale is answered, so the prefixed class stands whatever is written, beside the model's own
`MVK_SUPP_LANGUAGES_MISSING`, while the unprefixed one asks nothing (rows `n-no-locale` and
`n-no-locale-nomsg` of the [sort-list supplement](../../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity)). -/
def messagePresence (declaredLocales : List String) (entries : List (String × String)) :
    MessagePresence :=
  if declaredLocales.isEmpty then { prefixed := [.errorMessageMissing] } else
  let answered := declaredLocales.filter fun locale =>
    (judgedText entries locale).any (!ExecutableDeclaration.blank ·)
  { prefixed :=
      if answered.isEmpty then [.errorMessageMissing]
      else if answered.length < declaredLocales.length then [.errorMessageForLanguageMissing]
      else []
    unprefixed := declaredLocales.filterMap fun locale =>
      if (judgedText entries locale).all (·.isEmpty) then some .ruleHasNoErrorText else none }

/-- The error-text checker's template classes over every declared locale's nonempty judged text, in
locale order. A text for a locale the model does not declare is not asked (spec/11). `check` is the
template checker, reporting each failing parameter or the character gate that stops them. -/
def errorTextClasses (declaredLocales : List String) (entries : List (String × String))
    (check : String → List KernelStaticDiagnostic) : List KernelStaticDiagnostic :=
  declaredLocales.flatMap fun locale => match judgedText entries locale with
    | some text => if text.isEmpty then [] else check text
    | none => []

/-- What each member of one declaration drew from its own checker, before the report withholds. -/
structure DeclarationVerdicts where
  /-- The name and error-code classes. -/
  slots : List KernelStaticDiagnostic := []
  /-- A rule's error-target classes, empty for a sound target and for a computation. -/
  target : List KernelStaticDiagnostic := []
  /-- The DSL members' first raised positioned class. -/
  firstRaised : Option KernelStaticDiagnostic := none
  /-- The DSL members' relational classes. -/
  relational : List KernelStaticDiagnostic := []
  presence : MessagePresence := {}
  errorText : List KernelStaticDiagnostic := []
  deriving Repr, DecidableEq

namespace DeclarationVerdicts

/-- The declaration's refusal: its target's classes, else its DSL class. -/
def refusal (verdicts : DeclarationVerdicts) : List KernelStaticDiagnostic :=
  if !verdicts.target.isEmpty then verdicts.target
  else match verdicts.firstRaised with
    | some diagnostic => [diagnostic]
    | none => verdicts.relational

/-- The classes the Kernel reports for this declaration. -/
def report (verdicts : DeclarationVerdicts) : List KernelStaticDiagnostic :=
  verdicts.slots ++ verdicts.presence.prefixed ++ verdicts.refusal ++
    if verdicts.refusal.isEmpty then verdicts.presence.unprefixed ++ verdicts.errorText else []

end DeclarationVerdicts

end A12Kernel
