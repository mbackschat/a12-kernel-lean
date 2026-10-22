import A12Kernel.Elaboration.FieldTypeDeclarationNotification

/-! # Locks on the notifications a field's type declaration raises

Each group mirrors rows of the retained capture
`evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/` and cites them by id. The
assertion is the multiset of capture labels one field raises, sorted, because the Kernel reports a set
and its order carries no claim. A repeated label is a repeated notification with different parameters.
The reader aggregation over whole models is replayed by the evidence projection, not here.

The Java pattern compilation is a host capability: `javaCompiler` rejects only the one source the
capture shows as invalid Java, as the pattern-admission locks inject theirs.
-/

namespace A12Kernel.Conformance.FieldTypeDeclarationNotification

open A12Kernel

private def english : StringPatternMessageTokens := { field := "field", fieldValue := "field.value" }

private def javaCompiler : StringPatternCompiler :=
  fun source => if source == "(" then .rejected else .compiled fun _ => true

/-- The sorted labels one field raises, or the unbuilt-model label. -/
private def labels (declaration : FieldTypeDeclaration) (locales : List String := ["en_US"]) :
    List String :=
  match declaration.judge javaCompiler { declaredLocales := locales, messageTokens := english } with
  | .modelNotBuilt => [modelNotBuiltLabel]
  | .notifications raised => (raised.map (·.label)).mergeSort (· ≤ ·)

private def string (declaration : StringTypeDeclaration) : FieldTypeDeclaration := .string declaration

private def number (declaration : NumberTypeDeclaration) : FieldTypeDeclaration := .number declaration

private def custom (declaration : CustomTypeDeclaration) : FieldTypeDeclaration := .custom declaration

private def date (declaration : DateTypeDeclaration) : FieldTypeDeclaration := .date declaration

/-- A Time or DateTime body, which carries only a format. -/
private def temporal (format : Option String) : FieldTypeDeclaration := .temporal { format }

private def fragment (format : Option String) (youngerThan1900Check : Bool := false) :
    FieldTypeDeclaration := .dateFragment { format, youngerThan1900Check }

private def dateRange (format separator : Option String) : FieldTypeDeclaration :=
  .dateRange { format, separator }

/-- An Enumeration whose values carry `(locale, text)` labels. -/
private def enumeration (values : List (String × List (String × String)))
    (rest : EnumerationTypeDeclaration := {}) : FieldTypeDeclaration :=
  .enumeration { rest with values := values.map fun (token, labels) =>
    { token, labels := labels.map fun (locale, text) => { locale, text } } }

private def hint (locale : String) (values : List String) : HintListEntry := { locale, values }

/- Law 1, String and Custom lengths: `-1` is no bound, `0`, above 99999 and below `-1` each draw their
   own class, two defective members of one class draw it once, and the Custom type follows the String
   law (r-twin, r-above, r-zero-both, r-str-neg1, r-two, r-custom). -/
example :
    labels (string { minLength := some 1, maxLength := some 99999 }) = [] ∧
    labels (string { maxLength := some 100000 }) = ["codeless:member-above-99999"] ∧
    labels (string { minLength := some 0, maxLength := some 0 }) = ["codeless:member-not-positive"] ∧
    labels (string { minLength := some (-1), maxLength := some (-1) }) = [] ∧
    labels (string { minLength := some (-2), maxLength := some 100000 }) =
      ["codeless:member-above-99999", "codeless:member-signed"] ∧
    labels (custom { name := some "Sig", maxLength := some 100000 }) =
      ["codeless:member-above-99999"] := by
  native_decide

/- Law 1, Number: `-1` is a signed length rather than no bound; the integer digits and the fractional
   counts have their own ceilings, a fractional `-1` is admitted, and a member refused as signed in
   three places is one notification (r-num-neg1, r-int16, r-int15, r-frac-neg2, r-sign-dedup). -/
example :
    labels (number { maxFractionalDigits := some 0, maxLength := some (-1) }) =
      ["codeless:member-signed"] ∧
    labels (number { maxFractionalDigits := some 0, maxIntegerDigits := some 16 }) =
      ["codeless:member-above-15"] ∧
    labels (number { maxFractionalDigits := some 0, maxIntegerDigits := some 15 }) = [] ∧
    labels (number { maxFractionalDigits := some 0, maxIntegerDigits := some 0 }) =
      ["codeless:member-not-positive"] ∧
    labels (number { minFractionalDigits := some (-2), maxFractionalDigits := some 2 }) =
      ["codeless:member-signed"] ∧
    labels (number { minFractionalDigits := some 2, maxFractionalDigits := some (-1) }) = [] ∧
    labels (number { maxIntegerDigits := some (-1), maxFractionalDigits := some (-2),
                     maxLength := some (-1) }) = ["codeless:member-signed"] := by
  native_decide

/- Law 1, Amount: with no `maxIntegerDigits` the derived count `15 - maxFractionalDigits` is judged
   like it, so a maximum of 15 fractional digits derives zero integer digits beside its own ceiling
   class, while an explicit count is never replaced (r-amount15). -/
example :
    labels (number { amount := true, maxFractionalDigits := some 15 }) =
      ["codeless:member-above-14", "codeless:member-not-positive"] ∧
    labels (number { amount := true, maxFractionalDigits := some 2 }) = [] ∧
    labels (number { amount := true, maxFractionalDigits := some 15, maxIntegerDigits := some 3 }) =
      ["codeless:member-above-14"] := by
  native_decide

/- Law 2, a String that skips value validation must permit line breaks, and the other combinations
   with it name their own classes once: a pattern or a minimum length counts, an empty pattern, a
   minimum of `-1` and a maximum do not (nv-1, nv-twin, pi-pattern, pi-min, pi-max, pi-both,
   pi-min-neg1, pi-pat-empty, pi-combo, lb1, lb1-twin-a, lb1-twin-b). -/
example :
    labels (string { noValueValidation := true }) =
      ["MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK"] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true }) = [] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true, pattern := some "[A-Z]+",
                     messages := [{ locale := "en_US", text := "bad" }] }) =
      ["MVK_STRING_TYPE_PARAMS_INCONSISTENT"] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true,
                     minLength := some 2 }) = ["MVK_STRING_TYPE_PARAMS_INCONSISTENT"] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true,
                     maxLength := some 2 }) = [] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true, minLength := some 2,
                     pattern := some "[A-Z]+", messages := [{ locale := "en_US", text := "bad" }] }) =
      ["MVK_STRING_TYPE_PARAMS_INCONSISTENT"] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true,
                     minLength := some (-1) }) = [] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true, pattern := some "",
                     messages := [{ locale := "en_US", text := "bad" }] }) =
      ["MVK_ERROR_MESSAGE_AND_NO_PATTERN"] ∧
    labels (string { noValueValidation := true, pattern := some "a++" }) =
      ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID", "MVK_PATTERN_INVALID",
        "MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK", "MVK_STRING_TYPE_PARAMS_INCONSISTENT"] := by
  native_decide

/- Law 2, a hint list with a skipped validation is a class of its own, an empty list is not, and the
   hint-value laws hold beside it; a permitted line break cannot meet a maximum of one (nh-1,
   nh-empty, nh-plus). -/
example :
    labels (string { noValueValidation := true, lineBreaksPermitted := true,
                     hintList := [hint "en_US" ["A"]] }) = ["MVK_NO_VAL_AND_HINT_LISTS"] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true, hintList := [] }) = [] ∧
    labels (string { noValueValidation := true, lineBreaksPermitted := true,
                     hintList := [hint "en_US" ["A", "A"]] }) =
      ["MVK_NO_VAL_AND_HINT_LISTS", "MVK_VALUES_DUPLICATE"] ∧
    labels (string { lineBreaksPermitted := true, maxLength := some 1 }) =
      ["MVK_LINE_BREAK_AND_MAX_LENGTH_1_INVALID"] ∧
    labels (string { maxLength := some 1 }) = [] ∧
    labels (string { lineBreaksPermitted := true, maxLength := some 2 }) = [] := by
  native_decide

/- Law 2 and 3, a minimum above a maximum needs both in range, for String and Number under the
   Kernel code and for Custom under its own; a bound that is already refused is never compared
   (mm-s, mm-s-eq, mm-s-neg, mm-n, mm-c, mm-c-oor). -/
example :
    labels (string { minLength := some 5, maxLength := some 3 }) =
      ["MVK_MIN_LENGTH_BIGGER_MAX_LENGTH"] ∧
    labels (string { minLength := some 3, maxLength := some 3 }) = [] ∧
    labels (string { minLength := some 2, maxLength := some (-1) }) = [] ∧
    labels (number { maxFractionalDigits := some 0, minLength := some 8, maxLength := some 4 }) =
      ["MVK_MIN_LENGTH_BIGGER_MAX_LENGTH"] ∧
    labels (custom { name := some "Sig", minLength := some 5, maxLength := some 3 }) =
      ["MIN_LENGTH_BIGGER_MAX_LENGTH"] ∧
    labels (custom { name := some "Sig", minLength := some 100000, maxLength := some 50 }) =
      ["codeless:member-above-99999"] := by
  native_decide

/- Law 2, a non-empty pattern meets the pattern admission gate whichever of its two stages refuses
   it; an empty pattern is no pattern for the message carrier too, and a pattern with a valid
   message is silent (p-bad, p-twin, p-nomsg, p-compile, p-empty). -/
example :
    labels (string { pattern := some "a{2}+", messages := [{ locale := "en_US", text := "bad" }] }) =
      ["MVK_PATTERN_INVALID"] ∧
    labels (string { pattern := some "a{2}", messages := [{ locale := "en_US", text := "bad" }] }) =
      [] ∧
    labels (string { pattern := some "a++" }) =
      ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID", "MVK_PATTERN_INVALID"] ∧
    labels (string { pattern := some "(", messages := [{ locale := "en_US", text := "bad" }] }) =
      ["MVK_PATTERN_INVALID"] ∧
    labels (string { pattern := some "", messages := [{ locale := "en_US", text := "bad" }] }) =
      ["MVK_ERROR_MESSAGE_AND_NO_PATTERN"] := by
  native_decide

/- Law 2, hint values: each distinct value outside the in-range bounds is one notification and each
   distinct repeated value one more, a locale the model does not declare is never judged and the same
   value in two locales is not a repeat (h-twin, h-long2, h-short, h-dup, h-undeclared, h-xlocale,
   h-oor, h-mixed). -/
example :
    labels (string { maxLength := some 3, hintList := [hint "en_US" ["AB", "ABC"]] }) = [] ∧
    labels (string { maxLength := some 3, hintList := [hint "en_US" ["ABCD", "WXYZ"]] }) =
      ["MVK_VALUE_TOO_LONG", "MVK_VALUE_TOO_LONG"] ∧
    labels (string { minLength := some 3, hintList := [hint "en_US" ["AB"]] }) =
      ["MVK_VALUE_TOO_SHORT"] ∧
    labels (string { hintList := [hint "en_US" ["A", "A", "A", "B", "B"]] }) =
      ["MVK_VALUES_DUPLICATE", "MVK_VALUES_DUPLICATE"] ∧
    labels (string { maxLength := some 3, hintList := [hint "de_DE" ["ABCD", "A", "A"]] }) = [] ∧
    labels (string { hintList := [hint "en_US" ["A"], hint "de_DE" ["A"]] }) ["en_US", "de_DE"] =
      [] ∧
    labels (string { maxLength := some 0, hintList := [hint "en_US" ["Basic"]] }) =
      ["codeless:member-not-positive"] ∧
    labels (string { minLength := some 2, maxLength := some 3,
                     hintList := [hint "en_US" ["ABCD", "A", "ABCD"]] }) =
      ["MVK_VALUES_DUPLICATE", "MVK_VALUE_TOO_LONG", "MVK_VALUE_TOO_SHORT"] := by
  native_decide

/- Law 2, a hint value holding a supplementary scalar is one codeless notification per field and is
   exempt from the three value laws whatever its length against the bounds; a sibling long value
   still draws its own class (h-unit, h-unit2, h-unit3, h-unit4, h-unit5, h-unit-mixed). -/
example :
    labels (string { maxLength := some 1, hintList := [hint "en_US" ["😀"]] }) =
      ["codeless:supplementary-character"] ∧
    labels (string { maxLength := some 1, hintList := [hint "en_US" ["😀😀"]] }) =
      ["codeless:supplementary-character"] ∧
    labels (string { minLength := some 3, hintList := [hint "en_US" ["😀😀"]] }) =
      ["codeless:supplementary-character"] ∧
    labels (string { maxLength := some 3, hintList := [hint "en_US" ["😀", "ABCD", "😀"]] }) =
      ["MVK_VALUE_TOO_LONG", "codeless:supplementary-character"] := by
  native_decide

/- Law 2, two hint-list entries for one locale leave the model unbuilt, which replaces every other
   notification of every field (h-twoentries). -/
example :
    labels (string { hintList := [hint "en_US" ["A"], hint "en_US" ["A"]] }) =
      ["codeless:model-not-built"] ∧
    (FieldTypeDeclaration.string { maxLength := some 100000,
                                   hintList := [hint "en_US" ["A"], hint "en_US" ["A"]] }).judge javaCompiler
        { declaredLocales := ["en_US"], messageTokens := english } = .modelNotBuilt := by
  native_decide

/- Law 3, a length above `15` plus one for the sign and one for a fractional part is too big; the
   fractional part is decided by either count and unknown when an undecided count could still make it
   true, in which case the check is silent (ml-17, ml-16, ml-pos, ml-frac, ml-frac17, ml-unknown,
   ml-decided, nl-17, nl-17-max17). -/
example :
    labels (number { maxFractionalDigits := some 0, maxLength := some 17 }) =
      ["MVK_MAX_LENGTH_TOO_BIG"] ∧
    labels (number { maxFractionalDigits := some 0, maxLength := some 16 }) = [] ∧
    labels (number { maxFractionalDigits := some 0, maxLength := some 16, positivesOnly := true }) =
      ["MVK_MAX_LENGTH_TOO_BIG"] ∧
    labels (number { maxLength := some 18, maxFractionalDigits := some 2 }) =
      ["MVK_MAX_LENGTH_TOO_BIG"] ∧
    labels (number { maxLength := some 17, maxFractionalDigits := some 2 }) = [] ∧
    labels (number { maxLength := some 17, minFractionalDigits := some (-2),
                     maxFractionalDigits := some 0 }) = ["codeless:member-signed"] ∧
    labels (number { maxLength := some 18, minFractionalDigits := some 15,
                     maxFractionalDigits := some 2 }) = ["MVK_MAX_LENGTH_TOO_BIG", "codeless:member-above-14"] ∧
    labels (number { maxFractionalDigits := some 0, minLength := some 17 }) =
      ["MVK_MIN_LENGTH_TOO_BIG"] ∧
    labels (number { maxFractionalDigits := some 0, minLength := some 17, maxLength := some 17 }) =
      ["MVK_MAX_LENGTH_TOO_BIG", "MVK_MIN_LENGTH_TOO_BIG"] := by
  native_decide

/- Law 3, both fractional counts `-1` is a class of its own beside the length law, which reads the
   `-1` pair as a decided, absent fractional part (ml-supp). -/
example :
    labels (number { maxLength := some 17, minFractionalDigits := some (-1),
                     maxFractionalDigits := some (-1) }) =
      ["MVK_FRACT_DIGITS_MISSING", "MVK_MAX_LENGTH_TOO_BIG"] := by
  native_decide

/- Law 3, a maximum length below the minimum fractional digits plus two reads only that minimum,
   whatever the sign setting or the state of the maximum count (ms-4, ms-5, ms-pos, ms-pos5,
   ms-oormax, ms-maxonly). -/
example :
    labels (number { maxLength := some 4, minFractionalDigits := some 3,
                     maxFractionalDigits := some 3 }) = ["MVK_MAX_LENGTH_TOO_SMALL"] ∧
    labels (number { maxLength := some 5, minFractionalDigits := some 3,
                     maxFractionalDigits := some 3 }) = [] ∧
    labels (number { maxLength := some 4, minFractionalDigits := some 3, maxFractionalDigits := some 3,
                     positivesOnly := true }) = ["MVK_MAX_LENGTH_TOO_SMALL"] ∧
    labels (number { maxLength := some 5, minFractionalDigits := some 3, maxFractionalDigits := some 3,
                     positivesOnly := true }) = [] ∧
    labels (number { maxLength := some 4, minFractionalDigits := some 3,
                     maxFractionalDigits := some 15 }) =
      ["MVK_MAX_LENGTH_TOO_SMALL", "codeless:member-above-14"] ∧
    labels (number { maxLength := some 4, minFractionalDigits := some 0,
                     maxFractionalDigits := some 3 }) = [] := by
  native_decide

/- Law 3, the fractional counts must be ordered when both are decided, and are silent when either is
   refused (ar-amount, r-silence). -/
example :
    labels (number { amount := true, maxFractionalDigits := some 2, minFractionalDigits := some 3 }) =
      ["MVK_ARITY_TOO_BIG", "MVK_FRACT_DIGITS_INVALID"] ∧
    labels (number { maxFractionalDigits := some 2, minFractionalDigits := some 3 }) =
      ["MVK_FRACT_DIGITS_INVALID"] ∧
    labels (number { maxFractionalDigits := some 3, minFractionalDigits := some 3 }) = [] ∧
    labels (number { minFractionalDigits := some 15, maxFractionalDigits := some 2 }) =
      ["codeless:member-above-14"] ∧
    labels (number { minFractionalDigits := some 3, maxFractionalDigits := some (-1) }) = [] := by
  native_decide

/- Law 3, the integer count plus the minimum fractional digits may not exceed 15, from the declared
   count or else the amount-derived one; a refused count is silent, the maximum fractional digits are
   never read, and a minimum of `-1` reads as zero, which cannot raise the sum because the integer
   count is itself at most 15 (ar-14+2, ar-13+2, ar-maxonly, ar-oor, ar-ml). -/
example :
    labels (number { maxIntegerDigits := some 14, minFractionalDigits := some 2,
                     maxFractionalDigits := some 2 }) = ["MVK_ARITY_TOO_BIG"] ∧
    labels (number { maxIntegerDigits := some 13, minFractionalDigits := some 2,
                     maxFractionalDigits := some 2 }) = [] ∧
    labels (number { maxIntegerDigits := some 14, minFractionalDigits := some 0,
                     maxFractionalDigits := some 2 }) = [] ∧
    labels (number { maxIntegerDigits := some 16, minFractionalDigits := some 2,
                     maxFractionalDigits := some 2 }) = ["codeless:member-above-15"] ∧
    labels (number { maxIntegerDigits := some 14, minFractionalDigits := some 2,
                     maxFractionalDigits := some 2, maxLength := some 18 }) =
      ["MVK_ARITY_TOO_BIG", "MVK_MAX_LENGTH_TOO_BIG"] ∧
    labels (number { maxIntegerDigits := some 15, minFractionalDigits := some (-1),
                     maxFractionalDigits := some 2 }) = [] := by
  native_decide

/- Law 3, a minimum value above the maximum compares the bounds as the runtime prints them under the
   declared fractional counts, so the same authored bounds are ordered or not depending on how many
   digits the field keeps (mv-1, mv-eq, mv-neg, mv-num-a, mv-num-b, mv-num-c, mv-num-d). -/
example :
    labels (number { maxFractionalDigits := some 0, minValue := some 2, maxValue := some 1 }) =
      ["MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE"] ∧
    labels (number { maxFractionalDigits := some 0, minValue := some 1, maxValue := some 1 }) = [] ∧
    labels (number { maxFractionalDigits := some 0, minValue := some (-5), maxValue := some (-2) }) =
      [] ∧
    labels (number { maxFractionalDigits := some 0, minValue := some 1.4, maxValue := some 1 }) = [] ∧
    labels (number { maxFractionalDigits := some 1, minValue := some 1.4, maxValue := some 1 }) =
      ["MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE"] ∧
    labels (number { maxFractionalDigits := some 2, minValue := some 1.0, maxValue := some 1 }) = [] ∧
    labels (number { maxFractionalDigits := some 1, minFractionalDigits := some 1,
                     minValue := some 1.06, maxValue := some 1.1 }) = [] := by
  native_decide

/- Law 4, a Custom name that is absent, empty or Java-blank is missing; a non-blank name with a
   character outside ASCII letters, digits and underscore has a class of its own, and a digit-initial
   or underscore-initial name is admitted (cn-1, cn-ws, cn-space, cn-empty, cn-nobody, cn-nbsp,
   cn-alpha-0 to cn-alpha-8). -/
example :
    labels (custom { maxLength := some 5 }) = ["CUSTOM_FIELD_TYPE_CODENAME_MISSING"] ∧
    labels (custom { name := some "\x0b" }) = ["CUSTOM_FIELD_TYPE_CODENAME_MISSING"] ∧
    labels (custom { name := some " " }) = ["CUSTOM_FIELD_TYPE_CODENAME_MISSING"] ∧
    labels (custom { name := some "" }) = ["CUSTOM_FIELD_TYPE_CODENAME_MISSING"] ∧
    labels (custom {}) = ["CUSTOM_FIELD_TYPE_CODENAME_MISSING"] ∧
    labels (custom { name := some "\u00A0" }) = ["codeless:custom-name-content"] ∧
    labels (custom { name := some "Sig" }) = [] ∧
    labels (custom { name := some "1Sig" }) = [] ∧
    labels (custom { name := some "S_g" }) = [] ∧
    labels (custom { name := some "_S" }) = [] ∧
    labels (custom { name := some "Sä" }) = ["codeless:custom-name-content"] ∧
    labels (custom { name := some "S-g" }) = ["codeless:custom-name-content"] ∧
    labels (custom { name := some "S中" }) = ["codeless:custom-name-content"] ∧
    labels (custom { name := some "S g" }) = ["codeless:custom-name-content"] := by
  native_decide

/- Law 5, a partial Date precision needs a complete pure date format, an absent format is the
   complete date, the year check needs a year, and the two co-report rather than the first masking the
   second (od-1, od-twin, od-noformat, od-instant, od-both). -/
example :
    labels (date { format := some "yyyy-MM", partialMode := .dayOptional }) =
      ["MVK_OPTIONAL_DATE_TYPE_INVALID"] ∧
    labels (date { format := some "yyyy-MM-dd", partialMode := .dayOptional }) = [] ∧
    labels (date { partialMode := .dayOptional }) = [] ∧
    labels (date { format := some "yyyy-MM-dd'T'HH:mm:ss", partialMode := .dayOptional }) =
      ["MVK_OPTIONAL_DATE_TYPE_INVALID"] ∧
    labels (date { format := some "MM-dd", youngerThan1900Check := true,
                   partialMode := .dayOptional }) =
      ["MVK_ADDITIONAL_CHECK_INVALID", "MVK_OPTIONAL_DATE_TYPE_INVALID"] ∧
    labels (date { format := some "MM-dd", youngerThan1900Check := true }) =
      ["MVK_ADDITIONAL_CHECK_INVALID"] := by
  native_decide

/- Law 6, an unspecified type is one notification per field (u-1, u-body). -/
example : labels .unspecified = ["MVK_UNSPECIFIED_TYPE_NO_CODEGEN"] ∧ labels .other = [] := by
  native_decide

/- Law 7, the count of labelled values: once one value carries a label and another does not, every
   declared locale reports; a label for an undeclared locale is not counted (ec-1, ec-twin, ec-empty,
   ec-2loc, ec-undecl). -/
example :
    labels (enumeration [("A", [("en_US", "Alpha")]), ("B", [])]) =
      ["MVK_COUNT_OF_VALUES_INVALID"] ∧
    labels (enumeration [("A", [("en_US", "Alpha")]), ("B", [("en_US", "Beta")])]) = [] ∧
    labels (enumeration [("A", [("en_US", "Alpha"), ("de_DE", "AlphaDe")]), ("B", [])])
      ["en_US", "de_DE"] = ["MVK_COUNT_OF_VALUES_INVALID", "MVK_COUNT_OF_VALUES_INVALID"] ∧
    labels (enumeration [("A", [("fr_FR", "Alpha")]), ("B", [])]) = [] := by
  native_decide

/- Law 7, a carrying value needs a non-blank text in every declared locale, once per field however
   many locales fall short; a value that does not carry is not asked, and partial labelling beside a
   second locale draws both classes (ed-blank, ed-bi, ed-tri, ed-half, ec-2loc-partial, ec-2loc-de,
   ed-undecl, dd-incomplete). -/
example :
    labels (enumeration [("A", [("en_US", "Alpha")]), ("B", [("en_US", " ")])]) =
      ["MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"] ∧
    labels (enumeration [("A", [("en_US", "Alpha")]), ("B", [("en_US", "Beta")])]) ["en_US", "de_DE"] =
      ["MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"] ∧
    labels (enumeration [("A", [("en_US", "Alpha")]), ("B", [("en_US", "Beta")])])
      ["en_US", "de_DE", "fr_FR"] = ["MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"] ∧
    labels (enumeration [("A", [("en_US", "Alpha"), ("de_DE", "AlphaDe")]), ("B", [("en_US", "Beta")])])
      ["en_US", "de_DE"] = ["MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"] ∧
    labels (enumeration [("A", [("en_US", "Alpha")]), ("B", [])]) ["en_US", "de_DE"] =
      ["MVK_COUNT_OF_VALUES_INVALID", "MVK_COUNT_OF_VALUES_INVALID",
        "MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"] ∧
    labels (enumeration [("A", [("de_DE", "AlphaDe")]), ("B", [])]) ["en_US", "de_DE"] =
      ["MVK_COUNT_OF_VALUES_INVALID", "MVK_COUNT_OF_VALUES_INVALID",
        "MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"] ∧
    labels (enumeration [("A", [("fr_FR", "Alpha")]), ("B", [("fr_FR", "Beta")])]) = [] ∧
    labels (enumeration [("A", [("en_US", "Same")]), ("B", [("en_US", "Same")]), ("C", [])]) =
      ["MVK_COUNT_OF_VALUES_INVALID", "MVK_DISPLAY_VALUES_DUPLICATE"] := by
  native_decide

/- Law 7, a text shared by two values' labels in one declared locale is one notification per locale
   and text, compared case-sensitively and not across locales (dd-1, dd-x, dd-case, dd-two, dd-three,
   dd-2loc). -/
example :
    labels (enumeration [("A", [("en_US", "Same")]), ("B", [("en_US", "Same")])]) =
      ["MVK_DISPLAY_VALUES_DUPLICATE"] ∧
    labels (enumeration [("A", [("en_US", "X"), ("de_DE", "Y")]), ("B", [("en_US", "Y"), ("de_DE", "X")])])
      ["en_US", "de_DE"] = [] ∧
    labels (enumeration [("A", [("en_US", "Same")]), ("B", [("en_US", "same")])]) = [] ∧
    labels (enumeration [("A", [("en_US", "P")]), ("B", [("en_US", "P")]), ("C", [("en_US", "Q")]),
      ("D", [("en_US", "Q")])]) = ["MVK_DISPLAY_VALUES_DUPLICATE", "MVK_DISPLAY_VALUES_DUPLICATE"] ∧
    labels (enumeration [("A", [("en_US", "P")]), ("B", [("en_US", "P")]), ("C", [("en_US", "P")])]) =
      ["MVK_DISPLAY_VALUES_DUPLICATE"] ∧
    labels (enumeration [("A", [("en_US", "P"), ("de_DE", "R")]), ("B", [("en_US", "P"), ("de_DE", "R")])])
      ["en_US", "de_DE"] = ["MVK_DISPLAY_VALUES_DUPLICATE", "MVK_DISPLAY_VALUES_DUPLICATE"] := by
  native_decide

/- Law 7, a tab or pipe in a value token, a counted label text or a category token is one notification
   per distinct text in its own class; a label of an undeclared locale is not counted and a space is
   admitted (ev-tab, ev-pipe, ev-space, ev-both, ev-two, ed-tab, ed-tab-undecl, ecat-tab, ecat-tab2,
   ev-dup-tab, ev-tab-label-both). -/
example :
    labels (enumeration [("A\tB", []), ("C", [])]) = ["MVK_INTERNAL_VALUE_INVALID"] ∧
    labels (enumeration [("A|B", []), ("C", [])]) = ["MVK_INTERNAL_VALUE_INVALID"] ∧
    labels (enumeration [("A B", []), ("C", [])]) = [] ∧
    labels (enumeration [("A\t|B", []), ("C", [])]) = ["MVK_INTERNAL_VALUE_INVALID"] ∧
    labels (enumeration [("A\tB", []), ("C|D", [])]) =
      ["MVK_INTERNAL_VALUE_INVALID", "MVK_INTERNAL_VALUE_INVALID"] ∧
    labels (enumeration [("A", [("en_US", "Al\tpha")]), ("B", [("en_US", "Beta")])]) =
      ["MVK_DISPLAY_VALUE_INVALID"] ∧
    labels (enumeration [("A", [("fr_FR", "Al\tpha")]), ("B", [("fr_FR", "Beta")])]) = [] ∧
    labels (enumeration [("X\tY", []), ("Z", [])] { categories := [{ name := "Cat", tokens := ["X\tY", "Z"] }] }) =
      ["MVK_CATEGORY_VALUE_INVALID", "MVK_INTERNAL_VALUE_INVALID"] ∧
    labels (enumeration [("X", []), ("Z", [])] { categories := [{ name := "Cat", tokens := ["X\tY", "Z"] }] }) =
      ["MVK_CATEGORY_VALUE_INVALID"] ∧
    labels (enumeration [("A\tB", []), ("A\tB", [])]) =
      ["MVK_INTERNAL_VALUES_DUPLICATE", "MVK_INTERNAL_VALUE_INVALID", "codeless:repeated-value"] ∧
    labels (enumeration [("A\tB", [("en_US", "Al|pha")]), ("C", [("en_US", "Gamma")])]) =
      ["MVK_DISPLAY_VALUE_INVALID", "MVK_INTERNAL_VALUE_INVALID"] := by
  native_decide

/- Law 7, a line feed or carriage return in any text is one codeless notification per field and spares
   that text the tab and pipe class while its siblings keep theirs (nl-1, nl-mix, nl-pre). -/
example :
    labels (enumeration [("A\nB", []), ("C\rD", [])]) = ["codeless:line-break"] ∧
    labels (enumeration [("A\nB", []), ("C\tD", [])]) =
      ["MVK_INTERNAL_VALUE_INVALID", "codeless:line-break"] ∧
    labels (enumeration [("A\n\tB", []), ("C", [])]) = ["codeless:line-break"] ∧
    labels (enumeration [("A", [("en_US", "Al\npha")]), ("B", [("en_US", "Beta")])]) =
      ["codeless:line-break"] := by
  native_decide

/- Law 7, the default value must name a value token exactly, unless it is Java-blank; an empty value
   token draws nothing (sv-1, sv-a, sv-empty, sv-ws, sv-case, ev-empty-token). -/
example :
    labels (enumeration [("A", []), ("B", [])] { sValue := some "C" }) = ["MVK_S_VALUE_INVALID"] ∧
    labels (enumeration [("A", []), ("B", [])] { sValue := some "A" }) = [] ∧
    labels (enumeration [("A", []), ("B", [])] { sValue := some "" }) = [] ∧
    labels (enumeration [("A", []), ("B", [])] { sValue := some " " }) = [] ∧
    labels (enumeration [("A", []), ("B", [])] { sValue := some "a" }) = ["MVK_S_VALUE_INVALID"] ∧
    labels (enumeration [("", []), ("B", [])]) = [] := by
  native_decide

/- The default and the tokens are compared after Java's `String.trim`, which keeps a no-break space
   (peer `checkConsistency` rows at a12-dmkits `d26873580`, inbound 2026-10-18). -/
example :
    labels (enumeration [("BASIC", [])] { sValue := some " BASIC" }) = [] ∧
    labels (enumeration [("BASIC", [])] { sValue := some "BASIC " }) = [] ∧
    labels (enumeration [(" BASIC", [])] { sValue := some "BASIC" }) = [] ∧
    labels (enumeration [("BASIC", [])] { sValue := some "BA SIC" }) = ["MVK_S_VALUE_INVALID"] ∧
    labels (enumeration [("BASIC", [])] { sValue := some "\u00A0" }) = ["MVK_S_VALUE_INVALID"] := by
  native_decide

/- The Enumeration blocks the declaration owner already answers are part of the field's collection
   (o-3), and a field's own message classes are too: the Enumeration's invalid-value text meets the
   message gates, a String's message pairs with its pattern. -/
example :
    labels (enumeration [("A", []), ("A", [])]) =
      ["MVK_INTERNAL_VALUES_DUPLICATE", "codeless:repeated-value"] ∧
    labels (enumeration [("A", [])] { messages := [{ locale := "en_US", text := "a\tb" }] }) =
      ["INVALID_CHARACTERS"] ∧
    labels (string { messages := [{ locale := "en_US", text := "capitals" }] }) =
      ["MVK_ERROR_MESSAGE_AND_NO_PATTERN"] ∧
    labels (string { pattern := some "[A-Z]+" }) = ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID"] := by
  native_decide

/- Law 8, one thirteen-format vocabulary admits a declared format whatever the temporal kind, Date, Time,
   DateTime and DateFragment alike, and any other format draws one codeless notification per field; a
   Time field is admitted `yyyy-MM-dd` and refused `HH:mm`, and an absent format is the kind's default
   (tb-date-ok, tb-date-badfmt, tb-time-badfmt, tb-time-datefmt, tb-dt-badfmt, tb-frag-ok,
   tb-frag-badfmt). -/
example :
    ["yyyy-MM-dd", "dd.MM.yyyy", "yyyyMMdd", "yyyy", "yyyy-MM", "yyyyMM", "MM", "MM-dd", "MMdd",
        "ddMM", "HH:mm:ss", "yyyy-MM-dd'T'HH:mm:ss", "dd.MM."].all (fun format =>
      labels (date { format := some format }) == [] && labels (temporal (some format)) == [] &&
        labels (fragment (some format)) == []) = true ∧
    ["yyyy/MM/dd", "HH:mm", "yyyy-MM-dd HH:mm", "dd.MM", "ddMMyyyy", "dd.MM.yyyy'T'HH:mm:ss",
        ""].all (fun format =>
      labels (date { format := some format }) == ["codeless:date-format-invalid"] &&
        labels (temporal (some format)) == ["codeless:date-format-invalid"] &&
        labels (fragment (some format)) == ["codeless:date-format-invalid"]) = true ∧
    labels (date {}) = [] ∧ labels (temporal none) = [] ∧ labels (fragment none) = [] := by
  native_decide

/- A refused format binds nothing, as a refused member does: the partial-precision and pre-1900 laws
   that read the Date's components are silent beside it. No row measures the combination. -/
example :
    labels (date { format := some "yyyy/MM/dd", partialMode := .dayOptional, youngerThan1900Check := true })
      = ["codeless:date-format-invalid"] := by
  native_decide

/- Law 9, a DateFragment with the pre-1900 check needs a year in its format, by the Date law; its
   precision is not read (tb-frag-1900, tb-frag-1900-ok). -/
example :
    labels (fragment (some "dd.MM.") (youngerThan1900Check := true)) =
      ["MVK_ADDITIONAL_CHECK_INVALID"] ∧
    labels (fragment (some "dd.MM.yyyy") (youngerThan1900Check := true)) = [] ∧
    labels (fragment (some "dd.MM.")) = [] ∧
    labels (fragment (some "dd.MM") (youngerThan1900Check := true)) =
      ["codeless:date-format-invalid"] := by
  native_decide

/- Law 10, a DateRange pair must be on the allowlist, an absent separator being `/` and an absent
   format outside it; the month-only format alone admits the empty separator, and the year and
   1900 flags add nothing (tb-range-ok, tb-range-fmtonly, tb-range-fmtonly-de, tb-range-badpair,
   tb-range-badpair2, tb-range-sepnly, tb-range-1900, tb-range-interp). -/
example :
    labels (dateRange (some "yyyy-MM-dd") (some "/")) = [] ∧
    labels (dateRange (some "yyyy-MM-dd") none) = [] ∧
    labels (dateRange (some "dd.MM.yyyy") none) = ["codeless:date-range-format-invalid"] ∧
    labels (dateRange (some "dd.MM.yyyy") (some "/")) = ["codeless:date-range-format-invalid"] ∧
    labels (dateRange (some "dd.MM.yyyy") (some "-")) = [] ∧
    labels (dateRange (some "yyyyMM") (some "-")) = ["codeless:date-range-format-invalid"] ∧
    labels (dateRange none (some "/")) = ["codeless:date-range-format-invalid"] ∧
    labels (dateRange none none) = ["codeless:date-range-format-invalid"] ∧
    labels (dateRange (some "MM") (some "")) = [] ∧
    labels (dateRange (some "yyyy-MM-dd") (some "")) = ["codeless:date-range-format-invalid"] ∧
    labels (dateRange (some "MM") (some "/")) = [] := by
  native_decide

/- Law 11, an Enumeration declaring no values, or an empty list of them, leaves the model unbuilt
   (tb-enum-novalues, tb-enum-emptyvalues); Boolean and Confirm fields draw nothing
   (tb-bool-body, tb-confirm-body). -/
example :
    labels (.enumeration {}) = [modelNotBuiltLabel] ∧
    labels (.enumeration { values := [], sValue := some "A" }) = [modelNotBuiltLabel] ∧
    labels (enumeration [("A", [])]) = [] ∧ labels .other = [] := by
  native_decide

end A12Kernel.Conformance.FieldTypeDeclarationNotification
