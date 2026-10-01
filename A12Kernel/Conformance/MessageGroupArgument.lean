import A12Kernel.Elaboration.MessageGroupArgument

/-! # Message group argument syntax conformance locks

What the group argument's decoder decides before any model is consulted: the lexical or syntax class
of a refused spelling, the retired class, and which alternative and authored path an admitted
spelling decodes to. Every expected value is a Kernel 30.8.1 class measured at the
[argument-layer](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)
and [argument-event](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events)
checkpoints or in the peer's grid ([inbound](../../docs/SOURCES.md#inbound-2026-10-01-group-arguments)),
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
    ruleGroup := "RuleGroup", rootGroup := "RootGroup", retired := ["Zeile", "Usb"],
    offset := ["Zeile"] }

private def refused (argument : String) : Option MessageGroupArgumentRefusal :=
  match decodeMessageGroupArgument keywords argument with
  | .error refusal => some refusal
  | .ok _ => none

private def decoded (argument : String) : Option (AuthoredMessageGroup × Bool) :=
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
is no token, and an up-step after a name, a turning point or a leading separator is a syntax fault. -/
example :
    syntaxFault "Head//%" .separator = true ∧
      (["Head/%", "Side%", "%Head", "RuleGroup%", "Zeile-1%"].all (syntaxFault · .lexer)) = true ∧
      ([",", "{", "}", "@", "=", "^"].all fun suffix =>
        syntaxFault s!"Head{suffix}" .lexer && syntaxFault s!"Nope{suffix}" .lexer) = true ∧
      (["Head/..", "..Order/..", "/..", "/../Head"].all (syntaxFault · .unexpected)) = true := by
  native_decide

/- `RuleGroup` is a keyword token and opens its alternative whatever follows, leaving the token after
it for the keyword's check to precede. `RootGroup` is also a name: the keyword alone, a path segment
before a separator, and a syntax fault before any other token. Quoted, it is only a name. -/
example :
    decoded "RuleGroup" = some (.ruleGroup, false) ∧
      decoded "RuleGroup/Deeper" = some (.ruleGroup, true) ∧
      decoded "RuleGroup-x" = some (.ruleGroup, true) ∧
      decoded "RuleGroup+1" = some (.ruleGroup, true) ∧
      decoded "RootGroup" = some (.rootGroup, false) ∧
      decoded "RootGroup/Inner" = some (.relative 0 none ["RootGroup", "Inner"], false) ∧
      decoded "'RootGroup'" = some (.relative 0 none ["RootGroup"], false) ∧
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
      decoded "Zeile/Head" = some (.relative 0 none ["Zeile", "Head"], false) ∧
      decoded "Usb/Head" = some (.relative 0 none ["Usb", "Head"], false) ∧
      decoded "'Zeile'-1" = some (.relative 0 none ["Zeile"], true) := by
  native_decide

/- A reserved word outside the quoting-exempt set is never a name, so it is a syntax fault wherever a
name is required; after a parent walk it is a token left after the path. An exempt word and a run of
digits are names, and a word after the parent walk is its turning point. -/
example :
    (["Head/RuleGroup", "/Order/RuleGroup", "For", "Head/For", "BaseYear", "Head/BaseYear"].all
        (syntaxFault · .unexpected)) = true ∧
      decoded "..RuleGroup" = some (.relative 1 none [], true) ∧
      decoded "..RootGroup" = some (.relative 1 (some "RootGroup") [], false) ∧
      decoded "Head/value" = some (.relative 0 none ["Head", "value"], false) ∧
      decoded "index/Head" = some (.relative 0 none ["index", "Head"], false) ∧
      decoded "123" = some (.relative 0 none ["123"], false) ∧
      decoded "Head/123" = some (.relative 0 none ["Head", "123"], false) := by
  native_decide

end A12Kernel.Conformance.MessageGroupArgument
