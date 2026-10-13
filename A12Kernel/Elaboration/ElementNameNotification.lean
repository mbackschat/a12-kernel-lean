import A12Kernel.Elaboration.FieldTypeDeclarationNotification
import A12Kernel.Elaboration.IndexAndSortDeclaration

/-! # A12Kernel.Elaboration.ElementNameNotification — notifications element names and group declarations raise

The Kernel's whole-model check reports the defects of an element's name, of a group's declaration and of
an element's texts in the same multiset as the field-type classes ([`FieldTypeDeclarationNotification`](FieldTypeDeclarationNotification.lean)),
measured against kernel 30.8.1 over the same retained capture
(`evidence/kernel-30.8.1/captures/field-declaration-notifications-2026-10-13/`; rows are cited by id) and
read against [spec/11](../../spec/11-messages-and-custom.md) and [spec/01](../../spec/01-data-model.md).

**The alphabet is the carrier's, not one law.** A field's name admits letters, digits, `_`, `:` and `.`,
a nested group's admits letters, digits, `_` and the German umlauts and `ß` and must begin with a letter
or `_`, and a root group's admits the same set with any first character of it. A name is judged only for
the carrier that declares it: the same spelling is refused on one and admitted on another.

**A path class is the first failing element's.** An element whose name draws `MVK_PATH_INVALID` or
`MVK_PATHS_INCONSISTENT` hands every element below it the group-path codeless notification and stops the
elements below from drawing a path class of their own, from drawing the `xml` group class, and from
reporting a field message; their own codeless shape, their `_A12_DV` name classes and their field-type
classes stay. `PathAbove` carries what a path hands down and `GroupNameJudgement.below` extends it.

Rule and computation names, and the lone-surrogate and repertoire texts, have their owners
([`DeclarationAdmission`](DeclarationAdmission.lean), [`FieldMessageCheck`](FieldMessageCheck.lean)); this
module maps the rule classes to capture labels and owns the vocabulary the whole-model comparison
restricts to.

Choices no row separates, recorded where they are made: a `/` inside a group name is a path class of its
own as inside a field name (no row); an `xml` root hands its prefix to the groups below it (no row below a
root); a path class on an ancestor withholds the own path class of a descendant whichever kind it is;
and a name beyond sixty characters is counted in Unicode scalars.

Not claimed: the Kernel's notification order, the declaring carrier of an element kind with no name rule
here (a rule or computation reaches only the supplementary-scalar notification of a refused ancestor),
and any name over a limit this module does not state.
-/

namespace A12Kernel

/-- A class an element's name or its group's declaration raises. The ones without a Kernel code are named by their own class label. -/
inductive ElementNameKind where
  | pathInvalid
  | pathsInconsistent
  | fieldNameShape
  | groupNameShape
  | rootNameShape
  | nameAboveSixty
  | supplementaryCharacter
  | fieldDigitInitial
  | fieldDotColon
  | fieldXmlPrefix
  | fieldValueWord
  | rootDigitInitial
  | groupXmlPrefix
  | groupUnderscore
  | rootGroupNameInvalid
  | maxTooBig
  | invalidSortInfo
  deriving Repr, DecidableEq

namespace ElementNameKind

def all : List ElementNameKind :=
  [pathInvalid, pathsInconsistent, fieldNameShape, groupNameShape, rootNameShape, nameAboveSixty,
    supplementaryCharacter, fieldDigitInitial, fieldDotColon, fieldXmlPrefix, fieldValueWord,
    rootDigitInitial, groupXmlPrefix, groupUnderscore, rootGroupNameInvalid, maxTooBig, invalidSortInfo]

def label : ElementNameKind → String
  | pathInvalid => "MVK_PATH_INVALID"
  | pathsInconsistent => "MVK_PATHS_INCONSISTENT"
  | fieldNameShape => "codeless:field-name-shape"
  | groupNameShape => "codeless:group-name-shape"
  | rootNameShape => "codeless:root-name-shape"
  | nameAboveSixty => "codeless:name-above-sixty"
  | supplementaryCharacter => "codeless:supplementary-character"
  | fieldDigitInitial => "MVK_NAME_STARTS_WITH_DIGIT_A12_DV"
  | fieldDotColon => "MVK_NAME_INVALID_DOT_COLON_A12_DV"
  | fieldXmlPrefix => "MVK_NAME_STARTS_WITH_XML_A12_DV"
  | fieldValueWord => "MVK_NAME_INVALID_A12_DV"
  | rootDigitInitial => "MVK_NAME_STARTS_WITH_DIGIT"
  | groupXmlPrefix => "MVK_NAME_STARTS_WITH_XML"
  | groupUnderscore => "NAME_STARTS_WITH_UNDERSCORE_AND_WRONG_PATTERN"
  | rootGroupNameInvalid => "MVK_ROOT_GROUP_NAME_INVALID"
  | maxTooBig => "MVK_MAX_TOO_BIG"
  | invalidSortInfo => "MVK_INVALID_SORTINFO"

def isPathClass : ElementNameKind → Bool
  | pathInvalid | pathsInconsistent => true
  | _ => false

end ElementNameKind


/-- The judgement of a field's name. `kinds` are the classes the name draws before the path above is
considered, and `pathClass` says whether the name carries a path class of its own. -/
structure FieldNameJudgement where
  kinds : List ElementNameKind
  pathClass : Bool
  deriving Repr, DecidableEq

/-- The judgement of a group's name. `descendantCodeless` is the codeless notification the group hands to
every element below it; `startsWithXml` is the prefix fact a group below inherits. -/
structure GroupNameJudgement where
  kinds : List ElementNameKind
  pathClass : Bool
  descendantCodeless : List ElementNameKind
  startsWithXml : Bool
  deriving Repr, DecidableEq

/-- What the groups above an element hand down: whether one of them carries a path class, the codeless
notifications of their names, and whether one begins with `xml`. -/
structure PathAbove where
  pathClass : Bool := false
  codeless : List ElementNameKind := []
  xml : Bool := false
  deriving Repr, DecidableEq

private def asciiLetter (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') || ('A' ≤ character && character ≤ 'Z')

private def asciiDigit (character : Char) : Bool := '0' ≤ character && character ≤ '9'

private def umlauts : String := "äöüÄÖÜß"

private def fieldNameCharacter (character : Char) : Bool :=
  asciiLetter character || asciiDigit character || character == '_' || character == ':' ||
    character == '.'

private def groupNameCharacter (character : Char) : Bool :=
  asciiLetter character || asciiDigit character || character == '_' || umlauts.contains character

/-- Whether some dot is followed by anything but an ASCII letter, a trailing dot included. -/
private def dotBeforeNonLetter : List Char → Bool
  | '.' :: next :: rest => !asciiLetter next || dotBeforeNonLetter (next :: rest)
  | ['.'] => true
  | _ :: rest => dotBeforeNonLetter rest
  | [] => false

private def beginsWithXml (name : String) : Bool := name.toLower.startsWith "xml"

/-- A field name's classes. `valueWord` is the condition language's word for a value: a dotted name
ending in it, in any case, draws the invalid-name class. A `/` beside no other defect is a class of its
own, and beside any other defect counts as a refused character. A refused character or a dot before a
non-letter draws the path class and the field's codeless shape, replaced by the repertoire notification
when the name holds a supplementary scalar. Only a name with neither carries the `_A12_DV` name classes. -/
def fieldName (valueWord name : String) : FieldNameJudgement :=
  let characters := name.toList
  let slash := characters.contains '/'
  let refusedCharacter := characters.any fun c => c != '/' && !fieldNameCharacter c
  let dotBad := dotBeforeNonLetter characters
  if slash && !refusedCharacter && !dotBad then
    { kinds := [.pathsInconsistent], pathClass := true }
  else
    let refused := refusedCharacter || slash || dotBad
    let digitInitial := characters.head?.any asciiDigit
    let segments := name.splitOn "."
    let named : List ElementNameKind :=
      if refused then []
      else
        (if name.contains '.' || name.contains ':' then [.fieldDotColon] else []) ++
          (if digitInitial then [.fieldDigitInitial] else []) ++
          (if beginsWithXml name then [.fieldXmlPrefix] else []) ++
          (if name.contains '.' && (segments.getLast?.map String.toLower) == some valueWord.toLower
            then [.fieldValueWord] else [])
    let pathClass := refused || digitInitial
    { kinds := (if pathClass then [.pathInvalid] else []) ++
        (if refused then [if hasSupplementaryScalar name then .supplementaryCharacter else .fieldNameShape]
          else []) ++ named
      pathClass }

/-- The classes a field reports below `above`: its own, without a path class when one stands above, and
the codeless notification the groups above hand down. -/
def FieldNameJudgement.reported (judgement : FieldNameJudgement) (above : PathAbove) :
    List ElementNameKind :=
  ((if above.pathClass then judgement.kinds.filter fun kind => !kind.isPathClass else judgement.kinds) ++
    above.codeless).eraseDups

/-- A group name's classes by carrier. A nested group must begin with a letter or `_`; a root group may
begin with any character of the alphabet, and a leading digit is then a class of its own. A refusal is
the path class plus the group's shape, a root's own `root` shape, or the repertoire notification for a
supplementary scalar; more than sixty characters is the shape alone, a root's `above sixty`. A nested
group reserves a leading `_` for `__meta` and `__attachment_meta*`. Exactly `Id` in any case is a root
group's reserved name. -/
def groupName (isRoot : Bool) (name : String) : GroupNameJudgement :=
  let characters := name.toList
  let slash := characters.contains '/'
  let refusedCharacter := characters.any fun c => c != '/' && !groupNameCharacter c
  let leadingRefused := !isRoot && characters.head?.any fun c => !(asciiLetter c || c == '_')
  let refused := refusedCharacter || leadingRefused
  let long := 60 < name.length
  let reserved := if isRoot && name.toLower == "id" then [ElementNameKind.rootGroupNameInvalid] else []
  if slash && !refused then
    { kinds := [.pathsInconsistent] ++ reserved, pathClass := true, descendantCodeless := [],
      startsWithXml := beginsWithXml name }
  else
    let refused := refused || slash
    let handedDown : ElementNameKind :=
      if refused && hasSupplementaryScalar name then .supplementaryCharacter else .groupNameShape
    let ownShape : List ElementNameKind :=
      if refused then
        [if hasSupplementaryScalar name then .supplementaryCharacter
          else if isRoot then .rootNameShape else .groupNameShape]
      else []
    let ownLong : List ElementNameKind :=
      if long then [if isRoot then .nameAboveSixty else .groupNameShape] else []
    let named : List ElementNameKind :=
      if refused then []
      else if isRoot then
        (if characters.head?.any asciiDigit then [.rootDigitInitial] else [])
      else if characters.head? == some '_' && name != "__meta" &&
          !name.startsWith "__attachment_meta" then [.groupUnderscore]
      else []
    { kinds := (if refused then [.pathInvalid] else []) ++ ownShape ++ ownLong ++ named ++ reserved
      pathClass := refused
      descendantCodeless := if refused || long then [handedDown] else []
      startsWithXml := beginsWithXml name }

/-- The classes a group reports below `above`: its own, without a path class when one stands above,
the `xml` group class when the group or an ancestor begins with `xml` and no path class stands on the
group or above it, and the codeless notification the groups above hand down. -/
def GroupNameJudgement.reported (judgement : GroupNameJudgement) (above : PathAbove) :
    List ElementNameKind :=
  let xml := (judgement.startsWithXml || above.xml) && !judgement.pathClass && !above.pathClass
  ((if above.pathClass then judgement.kinds.filter fun kind => !kind.isPathClass else judgement.kinds) ++
    (if xml then [ElementNameKind.groupXmlPrefix] else []) ++ above.codeless).eraseDups

/-- What the group hands to the elements below it. -/
def GroupNameJudgement.below (judgement : GroupNameJudgement) (above : PathAbove) : PathAbove where
  pathClass := above.pathClass || judgement.pathClass
  codeless := (above.codeless ++ judgement.descendantCodeless).eraseDups
  xml := above.xml || judgement.startsWithXml

/-- The only notification a group above hands to a rule or computation: the repertoire one
(`ux-gname`, [spec/01 §1.1](../../spec/01-data-model.md#11-the-two-special-model-level-configurations)). -/
def PathAbove.forRule (above : PathAbove) : List ElementNameKind :=
  above.codeless.filter (· == .supplementaryCharacter)

/-- A repeatability beyond its carrier's ceiling and a non-repeatable group with sort fields. A group
declaring no repeatability, or one, is non-repeatable. A repeatability past a signed 32-bit count is not
read at all and raises no class, so the caller refuses it before asking here. -/
def groupDeclarationKinds (isRoot : Bool) (repeatability : Option Int) (sortFieldCount : Nat) :
    List ElementNameKind :=
  let ceiling : Int := if isRoot then 999999999 else 1999999999
  (if repeatability.any (ceiling < ·) then [.maxTooBig] else []) ++
    (if !repeatability.any (1 < ·) && 0 < sortFieldCount then [.invalidSortInfo] else [])

/-- The capture label of an executable declaration's class. The empty-code class is codeless and its
label is not retained, so it has none. -/
def DeclarationNotificationKind.label? : DeclarationNotificationKind → Option String
  | .reservedName => some KernelStaticDiagnostic.ruleNameInvalid.kernelCode
  | .missingCode => some KernelStaticDiagnostic.errorCodeMissing.kernelCode
  | .nameContent => some "codeless:rule-name-content"
  | .codeContent => some "codeless:code-content"
  | .emptyCode => none

/-- The capture label of a row-key declaration's refusal. -/
def RowFieldRefusal.label (refusal : RowFieldRefusal) : String :=
  refusal.kernelCode?.getD "codeless:sort-list-capacity"

/-- Every label the whole-model collection can produce: the field-type vocabulary, the name and group
classes, the executable declarations', the row-key refusals' and the encoding class. A comparison with
an observation restricts it to this vocabulary because the capture also records the classes of rule
conditions and computation operations, which are other owners'. -/
def declarationNotificationVocabulary : List String :=
  (fieldTypeNotificationVocabulary ++ ElementNameKind.all.map (·.label) ++
    [DeclarationNotificationKind.reservedName, .missingCode, .nameContent, .codeContent].filterMap
      (·.label?) ++
    RowFieldRefusal.all.map (·.label) ++ [KernelStaticDiagnostic.wrongEncoding.kernelCode]).eraseDups

end A12Kernel
