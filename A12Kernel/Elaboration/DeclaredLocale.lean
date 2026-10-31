/-! # A12Kernel.Elaboration.DeclaredLocale — a locale as the Kernel's reader builds it

The Kernel reads every locale spelling, a header's declared codes and each localized-text entry alike, into
a JDK `Locale`, and compares locales as those objects compare (spec/01 §1.1, the header locale codes
checkpoint `docs/sources/model-structure-and-declaration-probes.md#src-header-locale-codes`, measured
2026-10-29). `ParsedLocale` keeps the three components such a locale carries in the represented
profile, already normalized as the JDK's constructor normalizes them, and `key` is its `toString` form,
equal exactly where the locales are equal.

A header's declared locales fail the build on a locale with an empty language and on two codes naming one
locale. Two distinct locales sharing one JDK language tag instead draw `MVK_SUPP_LANGUAGES_DUPLICATE`, a
model-level class `languageTag` decides. -/

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

private def asciiAlnum (c : Char) : Bool := c.isAlphanum && c.toNat < 128

private def asciiLetters (text : String) : Bool := text.all fun c => c.isAlpha && c.toNat < 128

/-- The JDK's `toLanguageTag` of the locale, as spec/01 §1.1 states it over the measured pairs: a language
that is not 2–8 ASCII letters reads as `und`, a country that is not two ASCII letters or three ASCII
digits is left out, the variant subtags up to the first that is not 5–8 ASCII letters or digits, or four
opening with a digit, are kept, and that one and those after it follow as a private-use `lvariant`
sequence ending before the first subtag that is not 1–8 ASCII letters or digits. A locale with no country
and no kept subtag but such a sequence is tagged with no language. The locales the JDK tags specially,
such as `ja_JP_JP`, lie outside the represented profile. -/
def languageTag (locale : ParsedLocale) : String :=
  let languageWellFormed := (2 ≤ locale.language.length && locale.language.length ≤ 8) && asciiLetters locale.language
  let country :=
    if (locale.country.length == 2 && asciiLetters locale.country) ||
        (locale.country.length == 3 && locale.country.all fun c => c.isDigit && c.toNat < 128) then
      some locale.country
    else none
  let subtags := if locale.variant.isEmpty then [] else locale.variant.splitOn "_"
  let kept (subtag : String) :=
    subtag.all asciiAlnum &&
      ((5 ≤ subtag.length && subtag.length ≤ 8) || (subtag.length == 4 && subtag.front.isDigit))
  let variants := subtags.takeWhile kept
  let privateUse := (subtags.dropWhile kept).takeWhile fun subtag =>
    1 ≤ subtag.length && subtag.length ≤ 8 && subtag.all asciiAlnum
  let language :=
    if languageWellFormed then some locale.language
    else if country.isNone && variants.isEmpty && !privateUse.isEmpty then none
    else some "und"
  let privateTail := if privateUse.isEmpty then [] else "x" :: "lvariant" :: privateUse
  "-".intercalate (language.toList ++ country.toList ++ variants ++ privateTail)

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
