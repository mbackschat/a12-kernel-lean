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
`MVK_PATHS_INCONSISTENT` stops the elements below from drawing a path class of their own, from drawing the
`xml` group class, and from reporting a field message; their own codeless shape, their `_A12_DV` name
classes and their field-type classes stay. `PathAbove` carries what a path hands down and
`GroupNameJudgement.below` extends it.

**The group-path notification is a law over a path, not a name.** Each nested group is judged on its own
path and every field, rule and computation on its group's: the slash-joined names from the root, trimmed
whole by Java's `trim` (`groupPathRefused`). So a padded `Part` passes its own path and its fields' while
`Part/Bin` and everything below it fail, and a refused root's fields fail too
([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.7).

Rule and computation names, and the lone-surrogate and repertoire texts, have their owners
([`DeclarationAdmission`](DeclarationAdmission.lean), [`FieldMessageCheck`](FieldMessageCheck.lean)); this
module maps the rule classes to capture labels and owns the vocabulary the whole-model comparison
restricts to.

Choices no row separates, recorded where they are made: a `/` inside a group name is a path class of its
own as inside a field name (no row); an `xml` root hands its prefix to the groups below it (no row below a
root); a path class on an ancestor withholds the own path class of a descendant whichever kind it is;
and a name beyond sixty characters is counted in Unicode scalars.

Not claimed: the Kernel's notification order, which elements a name holding a `/` draws the path
notification at (the letter's rows are unexplained), and any name over a limit this module does not state.
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
  | maxValuesInvalid
  | countNotPositive
  | countSigned
  deriving Repr, DecidableEq

namespace ElementNameKind

def all : List ElementNameKind :=
  [pathInvalid, pathsInconsistent, fieldNameShape, groupNameShape, rootNameShape, nameAboveSixty,
    supplementaryCharacter, fieldDigitInitial, fieldDotColon, fieldXmlPrefix, fieldValueWord,
    rootDigitInitial, groupXmlPrefix, groupUnderscore, rootGroupNameInvalid, maxTooBig, invalidSortInfo,
    maxValuesInvalid, countNotPositive, countSigned]

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
  | maxValuesInvalid => "MVK_MAX_VALUES_INVALID"
  | countNotPositive => "codeless:count-not-positive"
  | countSigned => "codeless:count-signed"

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

/-- The judgement of a group's name. `startsWithXml` is the prefix fact a group below inherits. -/
structure GroupNameJudgement where
  name : String
  isRoot : Bool
  kinds : List ElementNameKind
  pathClass : Bool
  startsWithXml : Bool
  deriving Repr, DecidableEq

/-- What the groups above an element hand down: whether one of them carries a path class, their names
from the root, whether one begins with `xml`, and whether one declares a count below one. -/
structure PathAbove where
  pathClass : Bool := false
  groups : List String := []
  xml : Bool := false
  countInvalid : Bool := false
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

/-- Whether a field name draws the field's codeless shape: a refused character other than `/`, or a
dot before a non-letter. -/
def fieldNameShapeRefused (name : String) : Bool :=
  name.toList.any (fun c => c != '/' && !fieldNameCharacter c) || dotBeforeNonLetter name.toList

/-- Whether a group path fails the group-path law: its slash-joined names, trimmed whole by Java's
`trim`, must be a root part of the root alphabet and nested parts each beginning with an ASCII letter or
`_`, every part nonempty and at most sixty characters. No groups are no path and pass. -/
def groupPathRefused (groups : List String) : Bool :=
  !groups.isEmpty &&
  let part (leading : Char → Bool) (segment : String) : Bool :=
    segment.length ≤ 60 && match segment.toList with
      | [] => false
      | first :: rest => leading first && groupNameCharacter first && rest.all groupNameCharacter
  match (javaTrim ("/" ++ "/".intercalate groups)).splitOn "/" with
  | "" :: root :: nested => !part (fun _ => true) root || nested.any (!part (fun c => asciiLetter c || c == '_') ·)
  | _ => true

/-- The codeless notification a group path draws: the group-path one, or the repertoire one when the
path holds a supplementary scalar. -/
def groupPathCodeless (groups : List String) : List ElementNameKind :=
  if groupPathRefused groups then
    [if groups.any hasSupplementaryScalar then .supplementaryCharacter else .groupNameShape]
  else []

/-- A field name's classes. `valueWord` is the condition language's word for a value: a dotted name
ending in it, in any case, draws the invalid-name class. A `/` beside no other defect is a class of its
own, and beside any other defect counts as a refused character. A refused character or a dot before a
non-letter draws the path class and the field's codeless shape, replaced by the repertoire notification
when the name holds a supplementary scalar. Only a name with neither carries the `_A12_DV` name classes. -/
def fieldName (valueWord name : String) : FieldNameJudgement :=
  let characters := name.toList
  let slash := characters.contains '/'
  let shapeRefused := fieldNameShapeRefused name
  if slash && !shapeRefused then
    { kinds := [.pathsInconsistent], pathClass := true }
  else
    let refused := shapeRefused || slash
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
the notification its group's path draws. -/
def FieldNameJudgement.reported (judgement : FieldNameJudgement) (above : PathAbove) :
    List ElementNameKind :=
  ((if above.pathClass then judgement.kinds.filter fun kind => !kind.isPathClass else judgement.kinds) ++
    groupPathCodeless above.groups).eraseDups

/-- A group name's classes by carrier. A nested group must begin with a letter or `_`; a root group may
begin with any character of the alphabet, and a leading digit is then a class of its own. A refusal of
the name as written is the path class; a nested group's shape is its path's (`groupPathCodeless`), while
a root draws its own shape, or the repertoire notification for a supplementary scalar, else its own
notification above sixty characters, one per value, judged on the trimmed name. A nested group reserves a
leading `_` for `__meta` and `__attachment_meta*`. Exactly `Id` in any case is a root group's reserved
name. -/
def groupName (isRoot : Bool) (name : String) : GroupNameJudgement :=
  let characters := name.toList
  let slash := characters.contains '/'
  let refusedCharacter := characters.any fun c => c != '/' && !groupNameCharacter c
  let leadingRefused := !isRoot && characters.head?.any fun c => !(asciiLetter c || c == '_')
  let refused := refusedCharacter || leadingRefused
  let reserved := if isRoot && name.toLower == "id" then [ElementNameKind.rootGroupNameInvalid] else []
  if slash && !refused then
    { name, isRoot, kinds := [.pathsInconsistent] ++ reserved, pathClass := true
      startsWithXml := beginsWithXml name }
  else
    let refused := refused || slash
    let trimmed := javaTrim name
    let rootOwn : List ElementNameKind :=
      if !isRoot then []
      else if trimmed.toList.any (!groupNameCharacter ·) then
        [if hasSupplementaryScalar trimmed then .supplementaryCharacter else .rootNameShape]
      else if 60 < trimmed.length then [.nameAboveSixty]
      else []
    let named : List ElementNameKind :=
      if refused then []
      else if isRoot then
        (if characters.head?.any asciiDigit then [.rootDigitInitial] else [])
      else if characters.head? == some '_' && name != "__meta" &&
          !name.startsWith "__attachment_meta" then [.groupUnderscore]
      else []
    { name, isRoot
      kinds := (if refused then [.pathInvalid] else []) ++ rootOwn ++ named ++ reserved
      pathClass := refused
      startsWithXml := beginsWithXml name }

/-- The classes a group reports below `above`: its own, without a path class when one stands above,
the `xml` group class when the group or an ancestor begins with `xml` and no path class stands on the
group or above it, and, for a nested group, the notification its own path draws. -/
def GroupNameJudgement.reported (judgement : GroupNameJudgement) (above : PathAbove) :
    List ElementNameKind :=
  let xml := (judgement.startsWithXml || above.xml) && !judgement.pathClass && !above.pathClass
  ((if above.pathClass then judgement.kinds.filter fun kind => !kind.isPathClass else judgement.kinds) ++
    (if xml then [ElementNameKind.groupXmlPrefix] else []) ++
    (if judgement.isRoot then [] else groupPathCodeless (above.groups ++ [judgement.name]))).eraseDups

/-- What the group hands to the elements below it. -/
def GroupNameJudgement.below (judgement : GroupNameJudgement) (above : PathAbove) : PathAbove where
  pathClass := above.pathClass || judgement.pathClass
  groups := above.groups ++ [judgement.name]
  xml := above.xml || judgement.startsWithXml
  countInvalid := above.countInvalid

/-- The notification a rule or computation draws from its group's path, as a field does (spec/01 §1.3). -/
def PathAbove.forRule (above : PathAbove) : List ElementNameKind :=
  groupPathCodeless above.groups

/-- A group's count classes. A count below one, or a present member read as no value such as JSON
`null`, is `MVK_MAX_VALUES_INVALID` with the codeless sentence of its sign: not positive for zero or no
value, signed below zero. The class falls once more at every group and field beneath the group,
whose own sentence it does not repeat ([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21),
§2.17); which sentence present text read as no value draws is unmeasured. -/
def groupCountKinds (repeatability : Option Int) (present : Bool) : List ElementNameKind :=
  match repeatability with
  | some count =>
      if count < 0 then [.maxValuesInvalid, .countSigned]
      else if count == 0 then [.maxValuesInvalid, .countNotPositive]
      else []
  | none => if present then [.maxValuesInvalid, .countNotPositive] else []

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
  | .supplementaryCharacter => some ElementNameKind.supplementaryCharacter.label

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
