import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.LegalCharset
import A12Kernel.Semantics.String

/-! # Executable declaration metadata admission

An importer or Explain consumer must distinguish unreadable members, failed model construction,
and actual notifications, including notifications without a class key. These checks cover rule and
computation names, a rule's error code and a computation name's code content; they do not claim a
complete model consistency report.
The phase and competing-slot evidence is owned by the C17 declaration checkpoint in
[model declarations](../../docs/sources/model-structure-and-declaration-probes.md).
-/

namespace A12Kernel

inductive DeclarationStringValue where
  | text (value : String)
  | unreadable
  deriving Repr, BEq, DecidableEq

inductive ExecutableDeclarationKind where
  /-- Absence is decoded as an empty string; explicit null or a container is unreadable. -/
  | rule (errorCode : DeclarationStringValue)
  | computation
  deriving Repr, BEq, DecidableEq

structure ExecutableDeclaration where
  group : List String
  name : String
  kind : ExecutableDeclarationKind
  /-- The variant filter deletes it, which leaves only the empty-code notification (spec/01 §1.3). -/
  deleted : Bool := false
  deriving Repr, BEq, DecidableEq

inductive DeclarationNotificationKind where
  | reservedName
  | missingCode
  | nameContent
  | codeContent
  | emptyCode
  /-- A supplementary scalar in a judged name or code, in place of that slot's classes. -/
  | supplementaryCharacter
  deriving Repr, BEq, DecidableEq

def DeclarationNotificationKind.diagnostic? : DeclarationNotificationKind → Option KernelStaticDiagnostic
  | .reservedName => some .ruleNameInvalid
  | .missingCode => some .errorCodeMissing
  | .nameContent | .codeContent | .emptyCode | .supplementaryCharacter => none

structure DeclarationNotification where
  declaration : List String
  kind : DeclarationNotificationKind
  deriving Repr, BEq, DecidableEq

inductive DeclarationAdmissionFailure where
  | unreadable (declaration : List String) (member : String)
  | buildFailure (declaration : List String)
  | notifications (findings : List DeclarationNotification)
  deriving Repr, BEq, DecidableEq

namespace ExecutableDeclaration

/-- Java blankness differs from both DSL whitespace and no-break-space trimming (spec/01 §3.2). -/
def blank (text : String) : Bool := text.toList.all fun char =>
  let n := char.toNat
  (9 ≤ n && n ≤ 13) || (28 ≤ n && n ≤ 32) || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x2006) || (0x2008 ≤ n && n ≤ 0x200A) ||
    n == 0x2028 || n == 0x2029 || n == 0x205F || n == 0x3000

private def asciiLetter (char : Char) : Bool :=
  ('a' ≤ char && char ≤ 'z') || ('A' ≤ char && char ≤ 'Z')

private def asciiDigit (char : Char) : Bool := '0' ≤ char && char ≤ '9'

/-- The rule-name field admits an ASCII letter followed by ASCII letters, digits or underscores,
up to 100 characters. The metamodel's formal check precedes its reserved-namespace rule. -/
def nameAdmitted (name : String) : Bool :=
  name.length ≤ 100 && match name.toList with
    | [] => false
    | first :: rest => asciiLetter first && rest.all (fun c => asciiLetter c || asciiDigit c || c == '_')

private def codeAdmitted (code : String) : Bool :=
  code.length ≤ 100 && code.toList.all (fun c =>
    asciiLetter c || asciiDigit c || c == '_' || c == ' ' || "ÄÖÜäöüß".contains c)

def path (declaration : ExecutableDeclaration) : List String := declaration.group ++ [declaration.name]

/-- Notifications from independent slots coexist. A computation's name is judged by the error-code
content law as well as the name law: `C-x` draws both classes, `Cä` and `1C` the name class alone
(capture rows `cpn-dash`, `cpn-umlaut`, `cpn-digit`), while a rule's name meets the name law only.
Both alphabets judge the text after Java's `trim`, and a slot holding a supplementary scalar draws the
repertoire notification instead of its own classes, once per declaration. A declaration the variant
filter deletes draws only the empty-code notification, which survives the filter (spec/01 §1.3).
The sequence is a stable local projection, not a claim about Kernel notification order or unrelated
consistency checks. -/
def notifications (declaration : ExecutableDeclaration) : List DeclarationNotification := Id.run do
  let mut findings := []
  let add := fun kind => ({ declaration := declaration.path, kind } : DeclarationNotification)
  let code? := match declaration.kind with
    | .rule (.text code) => some code
    | _ => none
  if declaration.deleted then
    return if code?.any (·.isEmpty) then [add .emptyCode] else []
  let name := javaTrim declaration.name
  let nameSupplementary := hasSupplementaryScalar name
  if !nameSupplementary then
    if !nameAdmitted name then
      findings := findings ++ [add .nameContent]
    else if name.toLower.startsWith "vk_vk" then
      findings := findings ++ [add .reservedName]
  if declaration.kind == .computation && !nameSupplementary && !codeAdmitted name then
    findings := findings ++ [add .codeContent]
  let mut codeSupplementary := false
  if let some code := code? then
    codeSupplementary := hasSupplementaryScalar code
    if blank code then findings := findings ++ [add .missingCode]
    else if !codeSupplementary && !codeAdmitted (javaTrim code) then findings := findings ++ [add .codeContent]
    if code.isEmpty then findings := findings ++ [add .emptyCode]
  if nameSupplementary || codeSupplementary then findings := findings ++ [add .supplementaryCharacter]
  return findings

/-- Read failures and construction failures suppress all declaration verdicts. Check the complete
batch before projecting any notifications, so a later unreadable declaration cannot leave an
earlier declaration's apparent verdict behind (peer KF420 and rule-slot competing-defect laws). -/
def admitAll (declarations : List ExecutableDeclaration) : Except DeclarationAdmissionFailure Unit := do
  if let some declaration := declarations.find? (fun d => !d.deleted && match d.kind with
      | .rule .unreadable => true | _ => false) then
    throw (.unreadable declaration.path "errorCode")
  if let some declaration := declarations.find? (fun d => !d.deleted && blank d.name) then
    throw (.buildFailure declaration.path)
  let findings := declarations.flatMap notifications
  if !findings.isEmpty then throw (.notifications findings)

end ExecutableDeclaration
end A12Kernel
