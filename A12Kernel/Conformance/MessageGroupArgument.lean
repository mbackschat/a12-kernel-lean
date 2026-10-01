import A12Kernel.Elaboration.MessageGroupArgument

/-! # Message group argument syntax conformance locks

What the group argument's decoder decides before any model is consulted: the lexical or syntax class
of a refused spelling, the retired class, and which alternative and authored path an admitted
spelling decodes to. Every expected value is a Kernel 30.8.1 class measured at the
[argument-layer](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers),
[argument-event](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events)
and [walk and dotted-name](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)
checkpoints or in the peer's grids ([inbound](../../docs/SOURCES.md#inbound-2026-10-01-group-arguments),
[inbound](../../docs/SOURCES.md#inbound-2026-10-01a-provenance)),
on spellings translated to this fixture's `Order`, `Head`, `Deeper` and `Side`. What a decoded group
then resolves to, and the classes its lookup and availability draw, are locked with the message
template in `Conformance/ValidationMessageAuthoring.lean`.
-/

namespace A12Kernel.Conformance.MessageGroupArgument

open A12Kernel

/-- The en_US parameter terminals, read off the Kernel's own English terminal bundle. -/
def englishReservedTerminals : List String :=
  ["For", "index", "RootGroup", "RuleGroup", "Usb", "Vordruckname", "Vordruckzeile", "BaseYear",
    "value", "Zeile"]

/-- The seven terminals this producer historically accepts unquoted inside an entity name. -/
def englishUnquotedTerminals : List String :=
  ["value", "RootGroup", "Zeile", "Usb", "index", "Vordruckzeile", "Vordruckname"]

private def keywords : MessageGroupKeywords :=
  { reserved := englishReservedTerminals, exempt := englishUnquotedTerminals,
    exemptNonFinal := ["value", "Vordruckzeile", "Vordruckname"],
    ruleGroup := "RuleGroup", rootGroup := "RootGroup", retired := ["Zeile", "Usb"],
    offset := ["Zeile"] }

private def refused (argument : String) : Option MessageGroupArgumentRefusal :=
  match decodeMessageGroupArgument keywords argument with
  | .error refusal => some refusal
  | .ok _ => none

private def decoded (argument : String) : Option (AuthoredMessageGroup × MessageGroupRemainder) :=
  (decodeMessageGroupArgument keywords argument).toOption

private def syntaxFault (argument : String) (fault : MessageGroupLexicalFault) : Bool :=
  refused argument = some (.syntax fault)

/- A character the lexer forms no token from, or a malformed quoted name, is the lexer class whatever
name it sits beside; a separator with no name after it is the truncated class at the end and the
separator class before another separator, so the empty segment's position decides. -/
example :
    (["Head[1]", "Head*", "Head%", "'1Head'", "Nope[1]", "/Order/Head[1]", "'Deeper", "/'Order/Head",
        "/''"].all (syntaxFault · .lexer)) = true ∧
      (["", "Nope/", "/Nope/", "Side/", "Deeper/", "/Order/"].all (syntaxFault · .truncated)) =
        true ∧
      (["Nope//Deeper", "Deeper//Deep", "//Order"].all (syntaxFault · .separator)) = true := by
  native_decide

/- A fault answers where the parser meets it: a doubled separator before a later lexer fault, a
lexer fault right after a separator or a complete alternative first. A message punctuation character
is no token, and an up-step after a name or a leading separator is a syntax fault; after a turning
point it is a fault the walk's check precedes. -/
example :
    syntaxFault "Head//%" .separator = true ∧
      (["Head/%", "Side%", "%Head", "RuleGroup%", "Zeile-1%"].all (syntaxFault · .lexer)) = true ∧
      ([",", "{", "}", "@", "=", "^"].all fun suffix =>
        syntaxFault s!"Head{suffix}" .lexer && syntaxFault s!"Nope{suffix}" .lexer) = true ∧
      (["Head/..", "/..", "/../Head"].all (syntaxFault · .unexpected)) = true ∧
      decoded "..Order/.." = some (.relative 1 (some "Order") [], .afterWalk .unexpected) := by
  native_decide

/- `RuleGroup` is a keyword token and opens its alternative whatever follows, leaving the token after
it for the keyword's check to precede. `RootGroup` is also a name: the keyword alone, a path segment
before a separator, and a syntax fault before any other token. Quoted, it is only a name. -/
example :
    decoded "RuleGroup" = some (.ruleGroup, .none) ∧
      decoded "RuleGroup/Deeper" = some (.ruleGroup, .trailing) ∧
      decoded "RuleGroup-x" = some (.ruleGroup, .trailing) ∧
      decoded "RuleGroup+1" = some (.ruleGroup, .trailing) ∧
      decoded "RootGroup" = some (.rootGroup, .none) ∧
      decoded "RootGroup/Inner" = some (.relative 0 none ["RootGroup", "Inner"], .none) ∧
      decoded "'RootGroup'" = some (.relative 0 none ["RootGroup"], .none) ∧
      syntaxFault "RootGroup-x" .unexpected = true ∧
      syntaxFault "RootGroup+1" .unexpected = true := by
  native_decide

/- The retired `Zeile` takes a signed offset and `Usb` none. A complete offset alternative draws the
retired class even with a token after it, a sign needs its digits, and a token continuing neither
the keyword nor a path is a syntax fault before any check. Before a separator either word is a path
segment, and quoting one makes it a name. -/
example :
    (["Zeile", "Zeile-1", "Zeile+1", "Zeile-1 x"].all fun argument =>
        refused argument = some (.retired "Zeile")) = true ∧
      refused "Usb" = some (.retired "Usb") ∧
      (["Zeile-", "Zeile+"].all (syntaxFault · .expectedToken)) = true ∧
      (["Zeile-1x", "Zeile-x", "Zeile x", "Usb-1", "Usb x", "Usb-"].all
        (syntaxFault · .unexpected)) = true ∧
      decoded "Zeile/Head" = some (.relative 0 none ["Zeile", "Head"], .none) ∧
      decoded "Usb/Head" = some (.relative 0 none ["Usb", "Head"], .none) ∧
      decoded "'Zeile'-1" = some (.relative 0 none ["Zeile"], .trailing) := by
  native_decide

/- A reserved word outside the quoting-exempt set is never a name, so it is a syntax fault wherever a
name is required; after a parent walk it is a token left after the path. An exempt word and a run of
digits are names, and a word after the parent walk is its turning point. -/
example :
    (["Head/RuleGroup", "/Order/RuleGroup", "For", "Head/For", "BaseYear", "Head/BaseYear"].all
        (syntaxFault · .unexpected)) = true ∧
      decoded "..RuleGroup" = some (.relative 1 none [], .trailing) ∧
      decoded "..RootGroup" = some (.relative 1 (some "RootGroup") [], .none) ∧
      decoded "Head/value" = some (.relative 0 none ["Head", "value"], .none) ∧
      decoded "index/Head" = some (.relative 0 none ["index", "Head"], .none) ∧
      decoded "123" = some (.relative 0 none ["123"], .none) ∧
      decoded "Head/123" = some (.relative 0 none ["Head", "123"], .none) := by
  native_decide

/- A run of two or more up-steps ending on a separator before a token that continues no name counts one
step more and leaves that token's fault for after the walk's check; a single up-step does not, and a
name after the separator ends the run where it was written. A fault after the walk, a lexer fault
included, waits for the walk, and a turning point keeps its first word only
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)). -/
example :
    decoded "../../RuleGroup" = some (.relative 3 none [], .afterWalk .unexpected) ∧
      decoded "../../" = some (.relative 3 none [], .afterWalk .expectedToken) ∧
      decoded "../..//" = some (.relative 3 none [], .afterWalk .unexpected) ∧
      decoded "../" = some (.relative 1 none [], .afterWalk .truncated) ∧
      decoded "../RuleGroup" = some (.relative 1 none [], .afterWalk .unexpected) ∧
      decoded "../../Head" = some (.relative 2 none ["Head"], .none) ∧
      decoded "../../Head//%" = some (.relative 2 none [], .afterWalk .separator) ∧
      syntaxFault "../../%" .lexer = true ∧
      decoded "../../-x" = some (.relative 3 none [], .afterWalk .unexpected) ∧
      decoded "../../123" = some (.relative 2 none ["123"], .none) ∧
      decoded "..Wrong/.." = some (.relative 1 (some "Wrong") [], .afterWalk .unexpected) ∧
      refused "Zeile-1.x" = some (.retired "Zeile") ∧
      (["Head.%", "Head.'x", "..Wrong.%"].all (syntaxFault · .lexer)) = true ∧
      decoded "..Wrong/" = some (.relative 1 (some "Wrong") [], .afterWalk .truncated) ∧
      decoded "..Wrong/%" = some (.relative 1 (some "Wrong") [], .afterWalk .lexer) ∧
      decoded "..Order.x" = some (.relative 1 (some "Order") [], .none) := by
  native_decide

/- A dotted continuation joins its name segment. An exempt word may continue a name, and end it unless
it is the value suffix or a form-pointer terminal; a keyword, a number or a digit-initial word
continues none and is left after the name. Quoted or keyword-and-name, the first word joins too. -/
example :
    decoded "Head.x.y" = some (.relative 0 none ["Head.x.y"], .none) ∧
      decoded "Head.x/Deeper" = some (.relative 0 none ["Head.x", "Deeper"], .none) ∧
      decoded "Head.'x'" = some (.relative 0 none ["Head.x"], .none) ∧
      decoded "Head.Zeile" = some (.relative 0 none ["Head.Zeile"], .none) ∧
      decoded "Head.value.x" = some (.relative 0 none ["Head.value.x"], .none) ∧
      decoded "RootGroup.x" = some (.relative 0 none ["RootGroup.x"], .none) ∧
      decoded "'Zeile'.x" = some (.relative 0 none ["Zeile.x"], .none) ∧
      (["Head.value", "Head.Vordruckzeile", "Head.RuleGroup", "Head.1", "Head."].all
        fun argument => decoded argument = some (.relative 0 none ["Head"], .trailing)) = true := by
  native_decide

/-- The de_DE parameter terminals, read off the Kernel's own German terminal bundle, with the quoting
exemption and the non-final exempt words in the same grammar roles as the English ones. -/
private def germanKeywords : MessageGroupKeywords :=
  { reserved := ["Fuer", "index", "LfdNr", "RegelKontext", "Usb", "Vordruckname",
      "Vordruckzeile", "Referenzjahr", "Wert", "Zeile"],
    exempt := ["Wert", "LfdNr", "Zeile", "Usb", "index", "Vordruckzeile", "Vordruckname"],
    exemptNonFinal := ["Wert", "Vordruckzeile", "Vordruckname"],
    ruleGroup := "RegelKontext", rootGroup := "LfdNr", retired := ["Zeile", "Usb"],
    offset := ["Zeile"] }

private def decodedGerman (argument : String) :
    Option (AuthoredMessageGroup × MessageGroupRemainder) :=
  (decodeMessageGroupArgument germanKeywords argument).toOption

private def germanRefused (argument : String) : Option MessageGroupArgumentRefusal :=
  match decodeMessageGroupArgument germanKeywords argument with
  | .error refusal => some refusal
  | .ok _ => none

private def germanSyntaxFault (argument : String) (fault : MessageGroupLexicalFault) : Bool :=
  germanRefused argument = some (.syntax fault)

/- Under the German condition language the same decisions fall on the German words, as the peer's
German rows measure ([inbound](../../docs/SOURCES.md#inbound-2026-10-01a-provenance)): `RegelKontext`
is a keyword whatever follows, `LfdNr` is the keyword alone and a path segment before a separator,
`Fuer` and `Referenzjahr` are never names, `RegelKontext` after a walk is a token left after it, `Wert` cannot end a dotted name, and the English
shorthands are ordinary names. -/
example :
    decodedGerman "RegelKontext" = some (.ruleGroup, .none) ∧
      (["RegelKontext/Loans", "RegelKontext-x", "RegelKontext+1"].all fun argument =>
        decodedGerman argument = some (.ruleGroup, .trailing)) = true ∧
      decodedGerman "LfdNr" = some (.rootGroup, .none) ∧
      decodedGerman "LfdNr/Archive" = some (.relative 0 none ["LfdNr", "Archive"], .none) ∧
      decodedGerman "'LfdNr'" = some (.relative 0 none ["LfdNr"], .none) ∧
      (["LfdNr-x", "LfdNr+1", "Usb-1", "Zeile-x", "Fuer", "Head/Fuer", "Referenzjahr"].all
        (germanSyntaxFault · .unexpected)) = true ∧
      decodedGerman "..RegelKontext" = some (.relative 1 none [], .trailing) ∧
      germanSyntaxFault "Zeile+" .expectedToken = true ∧
      (["Zeile", "Zeile-1", "Zeile+1 x"].all fun argument =>
        germanRefused argument = some (.retired "Zeile")) = true ∧
      germanRefused "Usb" = some (.retired "Usb") ∧
      decodedGerman "RootGroup" = some (.relative 0 none ["RootGroup"], .none) ∧
      decodedGerman "Head.Wert" = some (.relative 0 none ["Head"], .trailing) ∧
      decodedGerman "Head.LfdNr" = some (.relative 0 none ["Head.LfdNr"], .none) := by
  native_decide

end A12Kernel.Conformance.MessageGroupArgument
