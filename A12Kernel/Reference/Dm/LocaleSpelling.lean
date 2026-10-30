import A12Kernel.Elaboration.DeclaredLocale

/-! # The Kernel's locale spelling parser

Every locale the DM-JSON readers meet, a localized-text entry's, a header's declared code and the
condition language's, is read by this one parser. -/

namespace A12Kernel.Dm

/-- The locale the Kernel's locale parser, `LocaleUtils.toLocale` of commons-lang3 3.20.0 as the measured
runtime ships it, builds from `spelling`, or `none` where it refuses the spelling. The accepted shape is a lowercase two- or three-letter language,
optionally followed by an uppercase two-letter country or a three-digit area, and a nonempty variant
after a second separator; "_" and `-` both separate, "_" when present. A spelling may instead start with
its separator and an uppercase country, then optionally the same separator and a nonempty variant
(`_US`, `-US-x`), and the empty spelling is the root locale. In a two-segment spelling a three-digit area
is taken after any first segment, so "XX_123" parses while "XX_123_x" does not.

The rows are peer KF290's Kernel spellings and the jar's own verdicts, measured 2026-10-29
(`docs/sources/model-structure-and-declaration-probes.md#src-locale-spelling-grammar`). Two
cases depend on tables this account does not carry and are refused as outside the represented profile:
a bare two-letter uppercase spelling, which parses exactly when the JDK lists it as an ISO country
(`US` parses and `EN` does not), and a non-ASCII character, whose case and digit classes are Unicode's.
"ja_JP_JP" and "th_TH_TH", which the JDK's constructor extends with a calendar or numbering extension,
are outside it too. -/
def parseLocale? (spelling : String) : Except String (Option ParsedLocale) := do
  let chars := spelling.toList
  if chars.any (·.val ≥ 128) then
    throw s!"locale {spelling} carries a non-ASCII character, outside the represented profile"
  let language (part : List Char) := (part.length == 2 || part.length == 3) && part.all Char.isLower
  let country (part : List Char) := part.length == 2 && part.all Char.isUpper
  let area (part : List Char) := part.length == 3 && part.all Char.isDigit
  let built (language country variant : List Char) : Except String (Option ParsedLocale) := do
    let language := match (String.mk language).toLower with
      | "iw" => "he" | "ji" => "yi" | "in" => "id" | other => other
    let locale : ParsedLocale := { language, country := String.mk country, variant := String.mk variant }
    if locale.key == "ja_JP_JP" || locale.key == "th_TH_TH" then
      throw s!"locale {spelling} carries a JDK extension, outside the represented profile"
    return some locale
  match chars with
  | [] => built [] [] []
  | separator :: rest =>
      if chars.contains '#' || chars.length < 2 then return none
      if country chars then
        throw s!"locale {spelling} parses only if the JDK lists it as a country, outside the represented profile"
      if separator == '_' || separator == '-' then
        return match rest with
          | first :: second :: tail =>
              if !(first.isUpper && second.isUpper) then none
              else match tail with
                | [] => some { language := "", country := String.mk [first, second], variant := "" }
                | next :: variant =>
                    if next == separator && !variant.isEmpty then
                      some { language := "", country := String.mk [first, second], variant := String.mk variant }
                    else none
          | _ => none
      if language chars then return ← built chars [] []
      let separator := if chars.contains '_' then '_' else '-'
      let (head, afterHead) := chars.span (· != separator)
      match afterHead with
        | [] => return none
        | _ :: tail =>
            let (middle, afterMiddle) := tail.span (· != separator)
            match afterMiddle with
            | [] => if (language head && country middle) || area middle then built head middle [] else return none
            | _ :: variant =>
                if language head && (middle.isEmpty || country middle || area middle) && !variant.isEmpty then
                  built head middle variant
                else return none

end A12Kernel.Dm
