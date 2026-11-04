import Lean.Data.Json
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # Message-text rows that need a model reader, on kernel 31.1.1

Three families whose rows read a whole model or a checked rule, which the conformance modules of the message
producers cannot: an empty category name on a keyed parameter, an undeclared locale's message text that the
model build reads, and an alternative's precondition written empty. Every row is a12-dmkits's at `1124b523f`,
kernel 31.1.1; each section names its test class. -/

namespace A12Kernel.Dm.MessageText31Locks

open Lean A12Kernel

/-! ## An empty category name on a keyed parameter

Locked: a12-dmkits MessageParameterDecoderAgreementTest (`anEmptyCategoryNameOnAKeyedParameter`,
`anEmptyCategoryNameOnAnUnreadFieldPrecedesMembership`) at 1124b523f, kernel 31.1.1. The empty name is asked
before keyed membership and before a defective key, so a key the condition reads, one it does not read and a
repeatable group with no index field all draw `NO_CATEGORY`, while the same parameter with a declared category
is admitted, refused `MVK_INDEX_FOR_ERROR_TEXT_INVALID` and refused likewise. -/

private def enumeration (id : FieldId) (group : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl :=
  { id, name := "Verdict", groupPath := group, repeatableScope := scope, policy := { kind := .enumeration }
    enumeration := some { storedTokens := ["A", "B"], categories := [{ name := "Tone", tokens := ["Hi", "Lo"] }] } }

private def library : FlatModel := {
  fields := [
    { id := 0, name := "Branch", groupPath := ["Library"], policy := { kind := .string } },
    { id := 1, name := "Code", groupPath := ["Library", "Loans"], repeatableScope := [1],
      policy := { kind := .string } },
    enumeration 2 ["Library", "Loans"] [1], enumeration 3 ["Library", "Reviews"] [2]]
  repeatableGroups := [
    { level := 1, path := ["Library", "Loans"], repeatability := some 5, indexField := some 1 },
    { level := 2, path := ["Library", "Reviews"], repeatability := some 10 }] }

private def libraryModel : DmModel := {
  flat := library, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (group : GroupPath) (errorEntity condition : String) : DmRule :=
  { group, name := "Keyed", errorCode := "KEYED", severity := "ERROR", errorEntityRelPath := errorEntity, condition }

/-- The class a rule's message template draws, `admitted` for none, and `none` when the rule itself is not
checked. -/
private def templateClass (definition : DmRule) (template : String) : Option String := do
  match ← (checkValidationRule libraryModel .english definition).toOption with
  | .ordinary checked =>
      match elaborateValidationMessageTemplate library .english (.rule checked) template with
      | .ok _ => some "admitted"
      | .error error => some ((error.namedRuleDiagnostic?.map (·.kernelCode)).getD "unclassed")
  | .parallel _ => none

/-- A rule in `/Library` reading `Loans/Verdict` under the key `k1`. -/
private def keyed : DmRule :=
  rule ["Library"] "../Branch" "FieldFilled(Branch) And FieldFilled(/Library/Loans/Verdict For \"k1\")"

/-- A rule in `/Library/Reviews`, a repeatable group that declares no index field. -/
private def reviews : DmRule := rule ["Library", "Reviews"] "../Verdict" "FieldFilled(Verdict)"

example :
    templateClass keyed "$/Library/Loans/Verdict-> For \"k1\"$" = some "NO_CATEGORY" ∧
    templateClass keyed "$/Library/Loans/Verdict->Tone For \"k1\"$" = some "admitted" ∧
    templateClass keyed "$/Library/Loans/Verdict-> For \"k2\"$" = some "NO_CATEGORY" ∧
    templateClass keyed "$/Library/Loans/Verdict->Tone For \"k2\"$" =
      some "MVK_INDEX_FOR_ERROR_TEXT_INVALID" ∧
    templateClass reviews "$Verdict-> For \"k\"$" = some "NO_CATEGORY" ∧
    templateClass reviews "$Verdict->Tone For \"k\"$" = some "MVK_INDEX_FOR_ERROR_TEXT_INVALID" ∧
    templateClass reviews "$Verdict ->$" = some "NO_CATEGORY" := by
  native_decide

/-! ## An undeclared locale's message text, which the model build reads

Locked: a12-dmkits ErrorTextLocaleScopeLawsTest (`anUndeclaredLocalesParametersMustBeSpelledAsADeclaredTextSpellsThem`,
`whichEntriesTheErrorTextCheckerExamines`) at 1124b523f, kernel 31.1.1, KF659. The error-text check still never
examines such a text, but code generation looks its parameters up among the declared texts of the same message:
a parameter no declared text spells identically, an odd number of dollars and `$BaseYear$` the declared texts do
not spell leave the model unbuilt, while an empty pair, a control character and a field type's pattern message
build. A model the reader leaves unbuilt is an error of `readModel` and the one `model-not-built` label of the
declaration walk. A defective declared text keeps its own class and the build failure never comes; this account
cannot see a rule's text classes, so it withholds the label only beside a class the walk itself reports. -/

private def localized (entries : List (String × String)) : Json :=
  Json.arr (entries.map fun (locale, text) =>
    Json.mkObj [("locale", .str locale), ("text", .str text)]).toArray

private def element (kind name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str s!"/Order/{name}"), ("name", .str name), (kind, Json.mkObj body)]

private def orderFields : List Json := [
  element "Field" "Reference" [("fieldType", Json.mkObj [("type", "StringType")])],
  element "Field" "Amount" [("fieldType", Json.mkObj [("type", "NumberType"),
    ("NumberType", Json.mkObj [("maxFractionalDigits", 2)])])]]

private def rulesElement (messages : List (String × String)) : Json :=
  element "Rule" "ProbeRule" [("errorEntityRelPath", "../Reference"), ("errorCode", "PROBE"),
    ("errorCondition", "FieldNotFilled(Reference)"), ("severity", "ERROR"), ("errorMessage", localized messages)]

private def computationElement (messages : List (String × String)) : Json :=
  element "Computation" "AmountCalc" [("computedFieldRelPath", "../Amount"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("precondition", "FieldFilled(Reference)"),
      ("operation", "1")]]), ("errorMessage", localized messages)]

private def orderModel (elements : List Json) : Json :=
  checkedEntryFrame <| Json.mkObj [
    ("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")], Json.mkObj [("code", "de_DE")]])]),
    ("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [
      ("type", "Group"), ("id", "/Order"), ("name", "Order"),
      ("Group", Json.mkObj [("elements", Json.arr (orderFields ++ elements).toArray)])]])])])]

/-- What the two readers make of a model: whether the model reader refuses it and whether the declaration
walk reports it unbuilt. -/
private def builds (json : Json) : Option (Bool × Bool) := do
  let walk ← (fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true).toOption
  pure ((readModel json).isOk, !walk.any (·.1 == modelNotBuiltLabel))

private def wellFormed : String := "The reference is required."

private def declared (en de : String) : List (String × String) := [("en_US", en), ("de_DE", de)]

/-- A rule's message entries with one "fr_FR" text beside the declared two. -/
private def withFrench (en de fr : String) : List (String × String) := declared en de ++ [("fr_FR", fr)]

private def unbuilt : Option (Bool × Bool) := some (false, false)

private def built : Option (Bool × Bool) := some (true, true)

example :
    builds (orderModel [rulesElement (withFrench wellFormed wellFormed "Voir $Reference$")]) = unbuilt ∧
    builds (orderModel [rulesElement (withFrench "See $Reference$" "Siehe $Reference$" "Voir $Reference$")]) =
      built ∧
    builds (orderModel [rulesElement (withFrench "See $Reference$" "Siehe $Reference$"
      "Voir $/Order/Reference$")]) = unbuilt ∧
    builds (orderModel [rulesElement (withFrench wellFormed wellFormed "Voir $$ ici")]) = built ∧
    builds (orderModel [rulesElement (declared wellFormed wellFormed)]) = built := by
  native_decide

/- The three defects the peer's grid puts to the build beside a clean declared pair, and the declared twin that
   the checker would refuse, which builds because every declared spelling is among the declared texts. -/
example :
    builds (orderModel [rulesElement (withFrench wellFormed wellFormed "See $Nonexistent$")]) = unbuilt ∧
    builds (orderModel [rulesElement (withFrench wellFormed wellFormed "a\tb")]) = built ∧
    builds (orderModel [rulesElement (withFrench wellFormed wellFormed "a $ b")]) = unbuilt ∧
    builds (orderModel [rulesElement (withFrench wellFormed wellFormed "since $BaseYear$")]) = unbuilt ∧
    builds (orderModel [rulesElement (withFrench "from $BaseYear+1$" "ab $BaseYear+1$" "since $BaseYear$")]) =
      unbuilt ∧
    builds (orderModel [rulesElement (withFrench "See $Nonexistent$" "See $Nonexistent$"
      "Voir $Nonexistent$")]) = built := by
  native_decide

/- A computation's message follows the rule's. The last row is this account's choice and no peer row: the
   peer's rows spell a parameter in both declared texts or in neither, so a spelling present in one declared
   text only is read as spelled, which a measurement could overturn. -/
example :
    builds (orderModel [computationElement (withFrench wellFormed wellFormed "Voir $Reference$")]) = unbuilt ∧
    builds (orderModel [computationElement (withFrench "See $Reference$" "Siehe $Reference$"
      "Voir $Reference$")]) = built ∧
    builds (orderModel [rulesElement (withFrench "See $Reference$" wellFormed "Voir $Reference$")]) = built := by
  native_decide

/- A field type's pattern message for an undeclared locale is not read by the build, and a declared text that
   the checker would refuse is not a build failure of its own. -/
example :
    builds (orderModel [element "Field" "Code" [("fieldType", Json.mkObj [("type", "StringType"),
      ("StringType", Json.mkObj [("pattern", "[A-Z]+"), ("errorMessage",
        localized [("en_US", "capitals"), ("de_DE", "Grossbuchstaben"), ("fr_FR", "Voir $Nonexistent$")])])])]]) =
      built := by
  native_decide

/-! ## An alternative's precondition written empty

Locked: a12-dmkits CheckerEmptyMemberAgreementTest (`theCheckerAnswersAnEmptyOrAbsentMemberAsA12Does`, row
"a computation's precondition", a member whose empty and absent forms the Kernel answers differently) at
1124b523f, kernel 31.1.1. The class is `MVK_UNEXPECTED_TOKEN` per the peer's letter and spec/01 §1.2: the peer
test states the difference of the two forms, not the class. An absent precondition is admitted; a common
precondition and an operation written empty keep the parser's empty-text class. -/

private def sourceModel : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "Source", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form"], name := "Out", policy := { kind := .number { scale := 0, signed := true } } }] }

private def lowered (precondition : Option String) (operation : String := "1")
    (common : Option String := none) : String :=
  let computation : DmComputation := {
    group := ["Form"], name := "C", targetRelPath := "../Out", commonPrecondition := common
    alternatives := [{ precondition, operation }], errorCodesToSuppress := [] }
  match lowerComputation sourceModel .english computation with
  | .ok _ => "admitted"
  | .error refusal => s!"{refusal.construct}:{refusal.detail}"

example :
    lowered none = "admitted" ∧
    lowered (some "FieldFilled(Source)") = "admitted" ∧
    lowered (some "") = "Syntax:MVK_UNEXPECTED_TOKEN" ∧
    lowered none "" = "Syntax:MVK_INCOMPLETE_INPUT" ∧
    lowered none "1" (some "") = "Syntax:MVK_INCOMPLETE_INPUT" := by
  native_decide

/-- The reader keeps a present empty precondition, so the lowering above is what a model's computation meets. -/
example :
    ((readModel (orderModel [element "Computation" "AmountCalc" [("computedFieldRelPath", "../Amount"),
      ("computationAlternatives", Json.arr #[Json.mkObj [("precondition", ""), ("operation", "1")]])]])).toOption.map
      fun dm => dm.computations.map fun computation => computation.alternatives.map (·.precondition)) =
      some [[some ""]] ∧
    ((readModel (orderModel [element "Computation" "AmountCalc" [("computedFieldRelPath", "../Amount"),
      ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "1")]])]])).toOption.map
      fun dm => dm.computations.map fun computation => computation.alternatives.map (·.precondition)) =
      some [[none]] := by
  native_decide

end A12Kernel.Dm.MessageText31Locks
