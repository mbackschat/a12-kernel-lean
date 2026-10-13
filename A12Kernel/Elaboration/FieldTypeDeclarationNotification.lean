import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Elaboration.EnumerationDeclarationNotification
import A12Kernel.Elaboration.FieldMessageCheck
import A12Kernel.Semantics.NumberBound
import A12Kernel.Semantics.StringPattern
import A12Kernel.Semantics.TemporalFormat

/-! # A12Kernel.Elaboration.FieldTypeDeclarationNotification — notifications a field's type declaration raises

The Kernel's whole-model check reports a field-type declaration's defects as a **multiset** of notifications: the order carries no claim (two authored orders gave the same report, and the order is not the authored one), and identical notifications on one element collapse to one, so a notification is keyed by its element, its class and its parameters. This module is the per-field collection, measured against kernel 30.8.1 over a retained capture (`evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/`; rows are cited by id).

The input is a small read-model of the field's body after type-definition resolution, with raw `Int` members, so a member the Kernel refuses to read is still visible here. The model's declared locales, its condition language's message tokens, the model charset and the host's Java pattern compilation arrive as context.

**A member out of range binds nothing.** Each range-checked member is read as unbounded, admitted or refused. A refused member draws its own codeless range notification and every law that reads the member is silent (`r-silence`, `ml-unknown`, `mm-c-oor`, `h-oor`), so a defect that is already named is never named a second time under another class.

Choices no row separates, recorded where they are made: a declared but refused integer count is not replaced by the amount-derived one; two label entries for one value and locale are both counted; a repeated hint-list locale is judged whether or not the model declares it; the label texts of every declared locale are pooled for the tab, pipe and line-break classes, and a text shared by two locales is one notification.

Not claimed: element-name, group, rule, computation and annotation classes, the encoding class, empty groups, the Date-fragment and Time partial modes, notification order, a variant-filtered field (the caller does not ask), and the Enumeration invalid-character class under a restricted charset beyond what `EnumerationDeclaration.notifications` already answers.
-/

namespace A12Kernel

/-- A class a field-type declaration raises, with the Kernel code when it has one and its own class label otherwise (`label`). The Enumeration classes that `EnumerationDeclaration.notifications` already owns and a field's own message classes arrive through `FieldTypeNotification` instead. -/
inductive FieldTypeNotificationKind where
  | memberNotPositive
  | memberSigned
  | memberAbove99999
  | memberAbove15
  | memberAbove14
  | stringNoValueNoLineBreak
  | stringParamsInconsistent
  | noValueAndHintLists
  | lineBreakAndMaxLengthOne
  | minLengthBiggerMaxLength
  | customMinLengthBiggerMaxLength
  | patternInvalid
  | valueTooLong
  | valueTooShort
  | valuesDuplicate
  | supplementaryCharacter
  | fractDigitsMissing
  | fractDigitsInvalid
  | maxLengthTooBig
  | minLengthTooBig
  | maxLengthTooSmall
  | arityTooBig
  | minValueBiggerThanMaxValue
  | customNameMissing
  | customNameContent
  | optionalDateTypeInvalid
  | additionalCheckInvalid
  | unspecifiedTypeNoCodegen
  | countOfValuesInvalid
  | internalValuesAndDisplayValues
  | displayValuesDuplicate
  | internalValueInvalid
  | displayValueInvalid
  | categoryValueInvalid
  | lineBreak
  | sValueInvalid
  deriving Repr, DecidableEq

namespace FieldTypeNotificationKind

/-- Every class once, in declaration order. -/
def all : List FieldTypeNotificationKind :=
  [memberNotPositive, memberSigned, memberAbove99999, memberAbove15, memberAbove14,
    stringNoValueNoLineBreak, stringParamsInconsistent, noValueAndHintLists,
    lineBreakAndMaxLengthOne, minLengthBiggerMaxLength, customMinLengthBiggerMaxLength,
    patternInvalid, valueTooLong, valueTooShort, valuesDuplicate, supplementaryCharacter,
    fractDigitsMissing, fractDigitsInvalid, maxLengthTooBig, minLengthTooBig, maxLengthTooSmall,
    arityTooBig, minValueBiggerThanMaxValue, customNameMissing, customNameContent,
    optionalDateTypeInvalid, additionalCheckInvalid, unspecifiedTypeNoCodegen, countOfValuesInvalid,
    internalValuesAndDisplayValues, displayValuesDuplicate, internalValueInvalid,
    displayValueInvalid, categoryValueInvalid, lineBreak, sValueInvalid]

/-- The label the capture gives the class: its Kernel code, or `codeless:` and the class name. -/
def label : FieldTypeNotificationKind → String
  | memberNotPositive => "codeless:member-not-positive"
  | memberSigned => "codeless:member-signed"
  | memberAbove99999 => "codeless:member-above-99999"
  | memberAbove15 => "codeless:member-above-15"
  | memberAbove14 => "codeless:member-above-14"
  | stringNoValueNoLineBreak => "MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK"
  | stringParamsInconsistent => "MVK_STRING_TYPE_PARAMS_INCONSISTENT"
  | noValueAndHintLists => "MVK_NO_VAL_AND_HINT_LISTS"
  | lineBreakAndMaxLengthOne => "MVK_LINE_BREAK_AND_MAX_LENGTH_1_INVALID"
  | minLengthBiggerMaxLength => "MVK_MIN_LENGTH_BIGGER_MAX_LENGTH"
  | customMinLengthBiggerMaxLength => "MIN_LENGTH_BIGGER_MAX_LENGTH"
  | patternInvalid => "MVK_PATTERN_INVALID"
  | valueTooLong => "MVK_VALUE_TOO_LONG"
  | valueTooShort => "MVK_VALUE_TOO_SHORT"
  | valuesDuplicate => "MVK_VALUES_DUPLICATE"
  | supplementaryCharacter => "codeless:supplementary-character"
  | fractDigitsMissing => "MVK_FRACT_DIGITS_MISSING"
  | fractDigitsInvalid => "MVK_FRACT_DIGITS_INVALID"
  | maxLengthTooBig => "MVK_MAX_LENGTH_TOO_BIG"
  | minLengthTooBig => "MVK_MIN_LENGTH_TOO_BIG"
  | maxLengthTooSmall => "MVK_MAX_LENGTH_TOO_SMALL"
  | arityTooBig => "MVK_ARITY_TOO_BIG"
  | minValueBiggerThanMaxValue => "MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE"
  | customNameMissing => "CUSTOM_FIELD_TYPE_CODENAME_MISSING"
  | customNameContent => "codeless:custom-name-content"
  | optionalDateTypeInvalid => "MVK_OPTIONAL_DATE_TYPE_INVALID"
  | additionalCheckInvalid => "MVK_ADDITIONAL_CHECK_INVALID"
  | unspecifiedTypeNoCodegen => "MVK_UNSPECIFIED_TYPE_NO_CODEGEN"
  | countOfValuesInvalid => "MVK_COUNT_OF_VALUES_INVALID"
  | internalValuesAndDisplayValues => "MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"
  | displayValuesDuplicate => "MVK_DISPLAY_VALUES_DUPLICATE"
  | internalValueInvalid => "MVK_INTERNAL_VALUE_INVALID"
  | displayValueInvalid => "MVK_DISPLAY_VALUE_INVALID"
  | categoryValueInvalid => "MVK_CATEGORY_VALUE_INVALID"
  | lineBreak => "codeless:line-break"
  | sValueInvalid => "MVK_S_VALUE_INVALID"

end FieldTypeNotificationKind

/-- One notification: the class and the parameters that distinguish its occurrences on one element. -/
inductive FieldTypeNotification where
  | declared (kind : FieldTypeNotificationKind) (parameters : List String := [])
  /-- A class of the field's own messages, owned by `fieldMessageDiagnostics`. -/
  | message (diagnostic : KernelStaticDiagnostic)
  /-- A class of an ordinary Enumeration declaration, owned by `EnumerationDeclaration.notifications`. -/
  | enumerationBlock (notification : EnumerationDeclarationNotification)
  deriving Repr, DecidableEq

/-- What the check says about one field: the model cannot be built, or the notifications the field raises. -/
inductive FieldTypeJudgement where
  | modelNotBuilt
  | notifications (raised : List FieldTypeNotification)
  deriving Repr, DecidableEq

/-- The one label the capture gives a model that cannot be built, which carries no element. -/
def modelNotBuiltLabel : String := "codeless:model-not-built"

/-- One hint-list entry as the model writes it: the values for one locale. -/
structure HintListEntry where
  locale : String
  values : List String
  deriving Repr, DecidableEq

/-- A String body as authored; an absent member is `none`. The pattern is the source, absent or empty meaning no pattern. -/
structure StringTypeDeclaration where
  minLength : Option Int := none
  maxLength : Option Int := none
  noValueValidation : Bool := false
  lineBreaksPermitted : Bool := false
  pattern : Option String := none
  hintList : List HintListEntry := []
  messages : List FieldMessageEntry := []
  deriving Repr, DecidableEq

/-- A Number body as authored, with the members raw so a refused one is still visible. `amount` is the amount trait. -/
structure NumberTypeDeclaration where
  minLength : Option Int := none
  maxLength : Option Int := none
  maxIntegerDigits : Option Int := none
  minFractionalDigits : Option Int := none
  maxFractionalDigits : Option Int := none
  positivesOnly : Bool := false
  amount : Bool := false
  minValue : Option Rat := none
  maxValue : Option Rat := none
  deriving Repr, DecidableEq

/-- A Custom body as authored. -/
structure CustomTypeDeclaration where
  name : Option String := none
  minLength : Option Int := none
  maxLength : Option Int := none
  deriving Repr, DecidableEq

/-- A Date body as authored; the format is absent when the model leaves it out. -/
structure DateTypeDeclaration where
  format : Option String := none
  partialMode : TemporalPartialMode := .full
  youngerThan1900Check : Bool := false
  deriving Repr, DecidableEq

/-- One display label of an Enumeration value for a locale. -/
structure EnumerationLabel where
  locale : String
  text : String
  deriving Repr, DecidableEq

/-- One Enumeration value token with the labels authored for it, in any locale. -/
structure EnumerationValueDeclaration where
  token : String
  labels : List EnumerationLabel := []
  deriving Repr, DecidableEq

/-- An ordinary Enumeration body as authored. `sValue` is the default value token and `messages` the invalid-value text. -/
structure EnumerationTypeDeclaration where
  values : List EnumerationValueDeclaration := []
  categories : List EnumerationCategoryDeclaration := []
  sValue : Option String := none
  messages : List FieldMessageEntry := []
  deriving Repr, DecidableEq

/-- A field's type body after type-definition resolution. -/
inductive FieldTypeDeclaration where
  | string (declaration : StringTypeDeclaration)
  | number (declaration : NumberTypeDeclaration)
  | custom (declaration : CustomTypeDeclaration)
  | date (declaration : DateTypeDeclaration)
  | enumeration (declaration : EnumerationTypeDeclaration)
  | unspecified
  /-- A field type none of these classes concerns. -/
  | other
  deriving Repr, DecidableEq

/-- What the laws take from the model besides the field: its declared locales, the field message tokens of its condition language, and its charset. -/
structure FieldTypeContext where
  declaredLocales : List String
  messageTokens : StringPatternMessageTokens
  charset : LegalCharset := .defaultBmp

/-- The capture label of the notification. -/
def FieldTypeNotification.label : FieldTypeNotification → String
  | .declared kind _ => kind.label
  | .message diagnostic => diagnostic.kernelCode
  | .enumerationBlock .supplementaryCharacter => "codeless:supplementary-character"
  | .enumerationBlock (.repeatedValue _) => "codeless:repeated-value"
  | .enumerationBlock notification => notification.kernelCode?.getD "codeless:unclassified"

/-- Every label the field collection can produce: the classes above, the field-message classes, the
Enumeration blocks and the unbuilt-model label. A comparison with an observation restricts it to this
vocabulary because the capture also records classes of other owners. The message codes are the
codomain of `fieldMessageDiagnostics`, listed here rather than derived. -/
def fieldTypeNotificationVocabulary : List String :=
  FieldTypeNotificationKind.all.map (·.label) ++
    ([KernelStaticDiagnostic.invalidMessageLinebreak, .invalidMessageCharacters,
      .wrongNumberOfDollars, .invalidMessageParameter, .errorMessageAndPatternInvalid,
      .errorMessageAndNoPattern, .errorMessageForLanguageMissing].map (·.kernelCode)) ++
    ([.invalidCharacter "" 0, .supplementaryCharacter, .missingCategoryValue "" "",
      .missingInternalValue "" "", .categoryValueDuplicate "" "", .internalValuesDuplicate "",
      .repeatedValue ""].map fun notification =>
        (FieldTypeNotification.enumerationBlock notification).label) ++
    [modelNotBuiltLabel]

/-! ## Reading a range-checked member -/

/-- How one range-checked member reads: no bound declared, a value inside the range, or a defect that
draws its own codeless notification and binds nothing. -/
inductive MemberReading where
  | unbounded
  | admitted (value : Int)
  | refused (kind : FieldTypeNotificationKind)
  deriving Repr, DecidableEq

namespace MemberReading

/-- The value a dependent law may read, absent for an unbounded or refused member. -/
def value? : MemberReading → Option Int
  | admitted value => some value
  | _ => none

/-- The class a refused member draws. -/
def refusal? : MemberReading → Option FieldTypeNotificationKind
  | refused kind => some kind
  | _ => none

/-- A String, Custom or Number length, `1..99999`. A String or Custom `-1` is no bound; a Number's
`-1` is a signed length (`r-str-neg1`, `r-num-neg1`). -/
def length (minusOneUnbounded : Bool) : Option Int → MemberReading
  | none => unbounded
  | some value =>
      if value == -1 && minusOneUnbounded then unbounded
      else if value < 0 then refused .memberSigned
      else if value == 0 then refused .memberNotPositive
      else if 99999 < value then refused .memberAbove99999
      else admitted value

/-- A Number's integer digits, `1..15` (`r-int15`, `r-int16`). -/
def integerDigits : Option Int → MemberReading
  | none => unbounded
  | some value =>
      if value < 0 then refused .memberSigned
      else if value == 0 then refused .memberNotPositive
      else if 15 < value then refused .memberAbove15
      else admitted value

/-- A Number's fractional count, `0..14`, where an absent count is `0` and `-1` is admitted as the
suppressed count (`r-frac-neg2`, `r-silence`). -/
def fractionalDigits (declared : Option Int) : MemberReading :=
  let value := declared.getD 0
  if value < -1 then refused .memberSigned
  else if 14 < value then refused .memberAbove14
  else admitted value

end MemberReading

private def raiseIf (condition : Bool) (kind : FieldTypeNotificationKind)
    (parameters : List String := []) : List FieldTypeNotification :=
  if condition then [.declared kind parameters] else []

private def refusals (readings : List MemberReading) : List FieldTypeNotification :=
  readings.filterMap fun reading => reading.refusal?.map (.declared · [])

/-- Whether both bounds are in range and the minimum exceeds the maximum. -/
private def minExceedsMax : MemberReading → MemberReading → Bool
  | .admitted lowest, .admitted highest => highest < lowest
  | _, _ => false

/-! ## String -/

/-- The notifications of a hint list's values. Only an entry for a declared locale is judged. A value
holding a supplementary scalar is one notification for the field and is exempt from the three value
laws; the rest are judged per entry and per distinct value, against the bounds that are in range
(`h-twin` to `h-xlocale`, `h-unit` to `h-unit-mixed`). -/
private def hintValueNotifications (context : FieldTypeContext) (minLength maxLength : MemberReading)
    (entries : List HintListEntry) : List FieldTypeNotification :=
  let judged := entries.filter fun entry => context.declaredLocales.contains entry.locale
  raiseIf (judged.any fun entry => entry.values.any hasSupplementaryScalar) .supplementaryCharacter ++
    judged.flatMap fun entry =>
      let values := entry.values.filter fun value => !hasSupplementaryScalar value
      let parameters (value : String) := [entry.locale, value]
      (values.eraseDups.filter fun value => maxLength.value?.any (· < (value.length : Int))).map
          (.declared .valueTooLong <| parameters ·) ++
        (values.eraseDups.filter fun value => minLength.value?.any ((value.length : Int) < ·)).map
          (.declared .valueTooShort <| parameters ·) ++
        (values.eraseDups.filter fun value => 1 < values.count value).map
          (.declared .valuesDuplicate <| parameters ·)

/-- A locale listed twice in a hint list is a model the Kernel cannot build (`h-twoentries`). The
locale is compared whether or not the model declares it, which no row separates. -/
private def hintListLocaleRepeated (entries : List HintListEntry) : Bool :=
  (entries.map (·.locale)).eraseDups.length < entries.length

private def stringNotifications (compilePattern : StringPatternCompiler) (context : FieldTypeContext)
    (declaration : StringTypeDeclaration) : List FieldTypeNotification :=
  let minLength := MemberReading.length true declaration.minLength
  let maxLength := MemberReading.length true declaration.maxLength
  let hasPattern := declaration.pattern.any fun pattern => !pattern.isEmpty
  let patternRefused := declaration.pattern.any fun pattern =>
    !pattern.isEmpty && classifyStringPattern compilePattern pattern != .admitted
  let carrier := if hasPattern then FieldMessageCarrier.stringPattern else .stringNoPattern
  refusals [minLength, maxLength] ++
    raiseIf (declaration.noValueValidation && !declaration.lineBreaksPermitted)
      .stringNoValueNoLineBreak ++
    raiseIf (declaration.noValueValidation && (hasPattern || minLength.value?.isSome))
      .stringParamsInconsistent ++
    raiseIf (declaration.noValueValidation && !declaration.hintList.isEmpty) .noValueAndHintLists ++
    raiseIf (declaration.lineBreaksPermitted && maxLength == .admitted 1) .lineBreakAndMaxLengthOne ++
    raiseIf (minExceedsMax minLength maxLength) .minLengthBiggerMaxLength ++
    raiseIf patternRefused .patternInvalid ++
    hintValueNotifications context minLength maxLength declaration.hintList ++
    (fieldMessageDiagnostics context.messageTokens context.declaredLocales carrier
      declaration.messages).map .message

/-! ## Number -/

/-- Whether the fractional part is declared: decided by a count in range, undecided when a refused
count could still make it true. `-1` is a decided absence. -/
private def fractionalPartDeclared (minimum maximum : MemberReading) : Option Bool :=
  let positive : MemberReading → Option Bool
    | .admitted value => some (0 < value)
    | _ => none
  match positive minimum, positive maximum with
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- The integer count the arity and amount laws read: the declared one, else for an amount the count
its maximum fractional digits leave, `15` less the raw maximum with an absent maximum read as `0`
(`r-amount15`). A declared but refused count is not replaced by the derived one, which no row
separates. -/
private def integerCount (declaration : NumberTypeDeclaration) : MemberReading :=
  match declaration.maxIntegerDigits with
  | some _ => MemberReading.integerDigits declaration.maxIntegerDigits
  | none =>
      if declaration.amount then
        MemberReading.integerDigits (some (15 - declaration.maxFractionalDigits.getD 0))
      else .unbounded

/-- The declared bounds, ordered as the runtime prints them under the raw fractional counts, an absent
count read as `0` as the reader does. A bound outside the printable range is no comparison. -/
private def boundsMisordered (declaration : NumberTypeDeclaration) : Bool :=
  match declaration.minValue, declaration.maxValue with
  | some lowest, some highest =>
      let minimumDigits := declaration.minFractionalDigits.getD 0
      let maximumDigits := declaration.maxFractionalDigits.getD 0
      match NumberBound.printedValue? lowest minimumDigits maximumDigits,
          NumberBound.printedValue? highest minimumDigits maximumDigits with
      | some printedLowest, some printedHighest => printedHighest < printedLowest
      | _, _ => false
  | _, _ => false

/-- The Number laws. The arity law reads the minimum fractional count as admitted, so a `-1` minimum
reads as `0`. That choice is unmeasured and cannot change an outcome, because an admitted integer
count is at most `15` and `15 + 0` is not above it. -/
private def numberNotifications (declaration : NumberTypeDeclaration) : List FieldTypeNotification :=
  let minLength := MemberReading.length false declaration.minLength
  let maxLength := MemberReading.length false declaration.maxLength
  let integers := integerCount declaration
  let minimum := MemberReading.fractionalDigits declaration.minFractionalDigits
  let maximum := MemberReading.fractionalDigits declaration.maxFractionalDigits
  let tooBig (length : MemberReading) (kind : FieldTypeNotificationKind) :
      List FieldTypeNotification :=
    match length.value?, fractionalPartDeclared minimum maximum with
    | some limit, some fractional =>
        raiseIf ((15 : Int) + (if declaration.positivesOnly then 0 else 1) +
          (if fractional then 1 else 0) < limit) kind
    | _, _ => []
  refusals [minLength, maxLength, integers, minimum, maximum] ++
    raiseIf (declaration.minFractionalDigits == some (-1) &&
      declaration.maxFractionalDigits == some (-1)) .fractDigitsMissing ++
    (match minimum, maximum with
      | .admitted lowest, .admitted highest => raiseIf (0 ≤ highest && highest < lowest) .fractDigitsInvalid
      | _, _ => []) ++
    raiseIf (minExceedsMax minLength maxLength) .minLengthBiggerMaxLength ++
    tooBig maxLength .maxLengthTooBig ++ tooBig minLength .minLengthTooBig ++
    (match maxLength.value?, minimum.value? with
      | some length, some digits => raiseIf (0 < digits && length < digits + 2) .maxLengthTooSmall
      | _, _ => []) ++
    (match integers.value?, minimum.value? with
      | some integer, some digits => raiseIf (15 < integer + max digits 0) .arityTooBig
      | _, _ => []) ++
    raiseIf (boundsMisordered declaration) .minValueBiggerThanMaxValue

/-! ## Custom, Date, unspecified -/

private def customNameCharacter (character : Char) : Bool :=
  character.isAlphanum || character == '_'

private def customNotifications (declaration : CustomTypeDeclaration) : List FieldTypeNotification :=
  let name := declaration.name.getD ""
  let minLength := MemberReading.length true declaration.minLength
  let maxLength := MemberReading.length true declaration.maxLength
  refusals [minLength, maxLength] ++
    raiseIf (ExecutableDeclaration.blank name) .customNameMissing ++
    raiseIf (!ExecutableDeclaration.blank name && name.toList.any (!customNameCharacter ·))
      .customNameContent ++
    raiseIf (minExceedsMax minLength maxLength) .customMinLengthBiggerMaxLength

/-- A partial precision needs a complete pure date, and the year check needs a year. The two are asked
of the shared policy gate one at a time with the other disabled, because the gate itself returns only
its first defect and the Kernel reports both (`od-both`). -/
private def dateNotifications (declaration : DateTypeDeclaration) : List FieldTypeNotification :=
  let policy : TemporalTargetPolicy := {
    format := declaration.format.getD "yyyy-MM-dd"
    partialMode := declaration.partialMode
    youngerThan1900Check := declaration.youngerThan1900Check }
  let components := TemporalComponents.ofFormat policy.format
  raiseIf ({ policy with youngerThan1900Check := false }.errorFor? .date components ==
      some .partialModeRequiresFullDate) .optionalDateTypeInvalid ++
    raiseIf ({ policy with partialMode := .full }.errorFor? .date components ==
      some .youngerThan1900RequiresYear) .additionalCheckInvalid

/-! ## Enumeration -/

private def hasLineBreak (text : String) : Bool :=
  text.toList.any fun character => character == '\n' || character == '\r'

/-- Whether the text draws the tab-and-pipe classes: it holds either character and no line break,
which a line break excuses it from (`nl-pre`). -/
private def hasSeparator (text : String) : Bool :=
  !hasLineBreak text && text.toList.any fun character => character == '\t' || character == '|'

/-- The texts of one value's counted labels for a declared locale. -/
private def labelTexts (value : EnumerationValueDeclaration) (locale : String) : List String :=
  (value.labels.filter (·.locale == locale)).map (·.text)

private def carriesLabel (locales : List String) (value : EnumerationValueDeclaration) : Bool :=
  value.labels.any fun label => locales.contains label.locale

private def enumerationNotifications (context : FieldTypeContext)
    (declaration : EnumerationTypeDeclaration) : List FieldTypeNotification :=
  let locales := context.declaredLocales
  let values := declaration.values
  let tokens := values.map (·.token)
  let countedTexts := values.flatMap fun value =>
    (value.labels.filter fun label => locales.contains label.locale).map (·.text)
  let categoryTokens := declaration.categories.flatMap (·.tokens)
  let blockOwner : EnumerationDeclaration := {
    storedTokens := tokens
    displayFacts := values.flatMap fun value => value.labels.map fun label =>
      { stored := value.token, locale := label.locale, display := label.text }
    categories := declaration.categories }
  (blockOwner.notifications context.charset).map .enumerationBlock ++
    (if values.any (carriesLabel locales) && values.any (!carriesLabel locales ·) then
      locales.map fun locale => .declared .countOfValuesInvalid [locale]
    else []) ++
    raiseIf ((values.filter (carriesLabel locales)).any fun value => locales.any fun locale =>
      (labelTexts value locale).isEmpty || (labelTexts value locale).any ExecutableDeclaration.blank)
      .internalValuesAndDisplayValues ++
    locales.flatMap (fun locale =>
      let perValue := values.flatMap fun value => (labelTexts value locale).eraseDups
      (perValue.eraseDups.filter fun text => 1 < perValue.count text).map
        (.declared .displayValuesDuplicate [locale, ·])) ++
    (tokens.filter hasSeparator).map (.declared .internalValueInvalid [·]) ++
    (countedTexts.filter hasSeparator).map (.declared .displayValueInvalid [·]) ++
    (categoryTokens.filter hasSeparator).map (.declared .categoryValueInvalid [·]) ++
    raiseIf ((tokens ++ countedTexts ++ categoryTokens).any hasLineBreak) .lineBreak ++
    raiseIf (declaration.sValue.any fun sValue =>
      !ExecutableDeclaration.blank sValue && !tokens.contains sValue) .sValueInvalid ++
    (fieldMessageDiagnostics context.messageTokens locales .enumerationInvalidValue
      declaration.messages).map .message

/-! ## The judgement of one field -/

/-- The notifications the field's type declaration raises, or the unbuilt-model outcome. The pattern
admission needs the host's Java compilation, so the compiler is a parameter; the closed ASCII profiles
of `builtinStringPatternCompiler` refuse Java-valid sources they cannot execute, which this law would
then report as invalid patterns. Identical notifications collapse to one. -/
def FieldTypeDeclaration.judge (compilePattern : StringPatternCompiler) (context : FieldTypeContext) :
    FieldTypeDeclaration → FieldTypeJudgement
  | .string declaration =>
      if hintListLocaleRepeated declaration.hintList then .modelNotBuilt
      else .notifications (stringNotifications compilePattern context declaration).eraseDups
  | .number declaration => .notifications (numberNotifications declaration).eraseDups
  | .custom declaration => .notifications (customNotifications declaration).eraseDups
  | .date declaration => .notifications (dateNotifications declaration).eraseDups
  | .enumeration declaration => .notifications (enumerationNotifications context declaration).eraseDups
  | .unspecified => .notifications [.declared .unspecifiedTypeNoCodegen]
  | .other => .notifications []

end A12Kernel
