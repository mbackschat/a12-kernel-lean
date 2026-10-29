/-! # A12Kernel.Elaboration.DeclaredLocale — a locale as the Kernel's reader builds it

The Kernel reads every locale spelling, a header's declared codes and each localized-text entry alike, into
a JDK `Locale`, and compares locales as those objects compare (spec/01 §1.1, the header locale codes
checkpoint `docs/sources/model-structure-and-declaration-probes.md#src-header-locale-codes`, measured
2026-10-29). `ParsedLocale` keeps the three components such a locale carries in the represented
profile, already normalized as the JDK's constructor normalizes them, and `key` is its `toString` form,
equal exactly where the locales are equal.

A header's declared locales fail the build on a locale with an empty language and on two codes naming one
locale. Two distinct locales sharing one JDK language tag instead draw `MVK_SUPP_LANGUAGES_DUPLICATE`, a
model-level class this account does not produce. -/

namespace A12Kernel

/-- A locale's language, country and variant, the language lowercased and the withdrawn `iw`, `ji` and
`in` read as `he`, `yi` and `id`, the country and the variant as written. -/
structure ParsedLocale where
  language : String
  country : String
  variant : String
  deriving Repr, DecidableEq

namespace ParsedLocale

/-- The JDK's `toString` form: the components joined by "_", the country's separator kept when a variant
follows, so "_US", "de__1996" and "de_CH_1996". -/
def key (locale : ParsedLocale) : String :=
  if locale.variant.isEmpty then
    if locale.country.isEmpty then locale.language else s!"{locale.language}_{locale.country}"
  else s!"{locale.language}_{locale.country}_{locale.variant}"

end ParsedLocale

/-- Why a header's declared locales leave no model. -/
inductive DeclaredLocaleFailure where
  | languageEmpty (key : String)
  | repeated (key : String)
  deriving Repr, DecidableEq

/-- The first declared locale, in declaration order, that fails the build: one with an empty language, or
one an earlier code already declared. Which of two failing codes the Kernel names is unmeasured; both
leave no model and no class. -/
def declaredLocaleFailure? (locales : List ParsedLocale) : Option DeclaredLocaleFailure :=
  go locales []
where
  go : List ParsedLocale → List String → Option DeclaredLocaleFailure
    | [], _ => none
    | locale :: rest, seen =>
        if locale.language.isEmpty then some (.languageEmpty locale.key)
        else if seen.contains locale.key then some (.repeated locale.key)
        else go rest (locale.key :: seen)

end A12Kernel
