import A12Kernel.Elaboration.MessageParameterSyntax

/-! # The message group position's argument syntax

A rule message's `$#…$` parameter takes a group argument, and this module decodes its spelling: the
alternative the parameter grammar chooses over the shared lexer's tokens, and the lexical or
syntax class of the first token no alternative continues. It decides nothing about the model. Which
group an authored argument names, whether that group is available to the message, and when a token
left after it is refused belong to `checkMessageGroup` in `ValidationMessageAuthoring`, which consumes
this decoder.

The classes follow the order in which the Kernel's parser meets the argument, measured at the
[argument-event checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events).
-/

namespace A12Kernel

/-- What a decoded group argument still owes the parser after the part whose check runs first. The
Kernel runs a check as an action at the end of the grammar rule it belongs to, so a token or fault
after that rule answers only once the check passes. -/
inductive MessageGroupRemainder where
  | none
  /-- A token left after a complete path, refused `MVK_UNEXPECTED_TOKEN` only once the path resolves to
  an available group. -/
  | trailing
  /-- A fault the parser met after completing a parent walk. The walk's own check, a climb past the root
  and then the turning point, answers first, and no name after the walk is looked up. The decoded
  argument then carries the walk alone. -/
  | afterWalk (fault : MessageParameterFault)
  /-- A semantic-index key after the argument, with the events its decoding meets in order. The group's
  own lookup answers before them, and in this fragment the key's own gate refuses after them, since no
  condition here carries a key for the group to match. -/
  | keyed (events : List MessageParameterEvent)
  deriving Repr, DecidableEq

/-- A group-position argument as the author spelled it. The two keyword shorthands stay distinct from
a path, because what they denote is decided against the rule's group rather than at parsing. -/
inductive AuthoredMessageGroup where
  | ruleGroup
  | rootGroup
  | absolute (path : GroupPath)
  /-- A path from the rule's group: `parents` leading `..` steps, an optional turning point naming the
  group they reach, then `path` downwards. A bare word is `relative 0 none [word]`. -/
  | relative (parents : Nat) (turningPoint : Option String) (path : GroupPath)
  deriving Repr, DecidableEq

/-- Names after a separator, each separator demanding a name, beside the tokens left after the path.
The token after the last name is left for the caller, which meets a lexer fault there before running
any check. -/
private def parseGroupNamesAfterSlash :
    List ParameterToken → Except MessageParameterFault (List String × List ParameterToken)
  | [] => throw .truncated
  | token :: rest =>
      match token.name?, rest with
      | some (_, name), .slash :: more => do
          let (names, left) ← parseGroupNamesAfterSlash more
          pure (name :: names, left)
      | some (_, name), left => pure ([name], left)
      | none, _ =>
          match token with
          | .bad => throw .lexer
          | .slash => throw .separator
          | _ => throw .unexpected

/-- What is left after a path whose check runs when the parser meets the end of the argument: nothing,
a semantic-index key, or a token refused after it, a lexer fault answering at once. -/
private def remainderAfterPath (keywords : MessageParameterKeywords) :
    List ParameterToken → Except MessageParameterFault MessageGroupRemainder
  | [] => pure .none
  | .bad :: _ => throw .lexer
  | .keyword word :: after =>
      if word == keywords.forTerminal then
        pure (.keyed (decodeMessageKey keywords (after.length + 1) after).1)
      else pure .trailing
  | _ => pure .trailing

/-- The names after a complete parent walk. Every fault among them, a lexer fault included, answers
only after the walk's check, which runs when the walk's own rule ends
([inbound](../../docs/SOURCES.md#inbound-2026-10-01a-parent-walk-and-dotted-names)). -/
private def parseNamesAfterWalk (keywords : MessageParameterKeywords) (parents : Nat)
    (turningPoint : Option String) (tokens : List ParameterToken) :
    AuthoredMessageGroup × MessageGroupRemainder :=
  match parseGroupNamesAfterSlash tokens with
  | .ok (names, left) =>
      match remainderAfterPath keywords left with
      | .ok remainder => (.relative parents turningPoint names, remainder)
      | .error fault => (.relative parents turningPoint [], .afterWalk fault)
  | .error fault => (.relative parents turningPoint [], .afterWalk fault)

/-- The rest of a relative path after `parents` up-steps: another up-step after a separator, a turning
point written directly after the last up-step, then names after a separator.

The walk ends where the parser decides it ends, which is one token past the separator, so a lexer fault
there answers first. When that token continues no name, a run of two or more up-steps has taken its
last separator as part of the run and counts one step more, which is what turns `$#../../RuleGroup$`
from a walk reaching the root exactly into one past it; a single up-step does not, and the
[parent-walk rows](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)
measure both. A turning point is compared by its first word alone, so `$#..Probe.x$` names `Probe`. -/
private def parseGroupUpRun (keywords : MessageParameterKeywords) (parents : Nat) :
    List ParameterToken → Except MessageParameterFault (AuthoredMessageGroup × MessageGroupRemainder)
  | .slash :: .up :: rest => parseGroupUpRun keywords (parents + 1) rest
  | .slash :: .bad :: _ => throw .lexer
  | .slash :: rest =>
      match rest.head?.bind ParameterToken.name? with
      | some _ => pure (parseNamesAfterWalk keywords parents none rest)
      | none =>
          if parents = 1 then pure (parseNamesAfterWalk keywords parents none rest)
          else
            pure (.relative (parents + 1) none [],
              .afterWalk (if rest.isEmpty then .expectedToken else .unexpected))
  | [] => pure (.relative parents none [], .none)
  | .bad :: _ => throw .lexer
  | token :: rest =>
      match token.name? with
      | some (turningPoint, _) =>
          match rest with
          | .slash :: more => pure (parseNamesAfterWalk keywords parents (some turningPoint) more)
          | left => (.relative parents (some turningPoint) [], ·) <$> remainderAfterPath keywords left
      | none => (.relative parents none [], ·) <$> remainderAfterPath keywords (token :: rest)

/-- Parse a tokenized group path into its authored form and what is left after it. -/
private def parseGroupPath (keywords : MessageParameterKeywords) :
    List ParameterToken → Except MessageParameterFault (AuthoredMessageGroup × MessageGroupRemainder)
  | .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (.absolute names, ← remainderAfterPath keywords left)
  | .up :: rest => parseGroupUpRun keywords 1 rest
  | tokens => do
      let (names, left) ← parseGroupNamesAfterSlash tokens
      pure (.relative 0 none names, ← remainderAfterPath keywords left)

/-- A group argument's alternative: a group, by keyword or path, or a retired terminal, which the
Kernel recognizes in order to refuse it. -/
private inductive ParsedGroupArgument where
  | group (authored : AuthoredMessageGroup)
  | retired (terminal : String)

/-- The keyword alternative a word opens, if it is one of the group position's terminals. -/
private def groupKeyword? (keywords : MessageParameterKeywords) (word : String) :
    Option ParsedGroupArgument :=
  if word == keywords.ruleGroup then some (.group .ruleGroup)
  else if word == keywords.rootGroup then some (.group .rootGroup)
  else if keywords.retired.contains word then some (.retired word)
  else none

/-- Choose a group argument's alternative from its tokens, as the parameter grammar does, and fail at
the first token no alternative continues. Only an unquoted word can open a keyword alternative, which
is why quoting a terminal turns it back into a group name. A `keyword` token, such as `RuleGroup` in
English, opens its own alternative whatever follows it, and one that is no group terminal opens none.
A group terminal that is also a name, which `RootGroup`, `Zeile` and `Usb` are in English, is the
keyword at the end of the text, the first segment of a path before a separator or as the first word
of a dotted name, and an offset terminal's alternative before a sign; before any other token neither
reading continues, and that is a syntax refusal before any check. The Kernel's classes on each branch
are measured at the [argument-event
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events). -/
private def parseGroupArgument (keywords : MessageParameterKeywords) :
    List ParameterToken →
      Except MessageParameterFault (ParsedGroupArgument × MessageGroupRemainder)
  | [] => throw .truncated
  | .bad :: _ => throw .lexer
  | .keyword word :: rest =>
      match groupKeyword? keywords word with
      | some keyword => (keyword, ·) <$> remainderAfterPath keywords rest
      | none => throw .unexpected
  | .name word false :: rest =>
      let path := do
        let (group, remainder) ← parseGroupPath keywords (.name word false :: rest)
        pure (ParsedGroupArgument.group group, remainder)
      match groupKeyword? keywords word with
      | none => path
      | some keyword =>
          match rest with
          | [] => pure (keyword, .none)
          | .slash :: _ => path
          -- The keyed reading is the name's: only the path alternative takes a key.
          | .keyword key :: _ => if key == keywords.forTerminal then path else throw .unexpected
          | .sign _ :: after =>
              if keywords.offset.contains word then
                match after with
                | .number _ :: left => (keyword, ·) <$> remainderAfterPath keywords left
                | [] => throw .expectedToken
                | .bad :: _ => throw .lexer
                | _ => throw .unexpected
              else throw .unexpected
          | .bad :: _ => throw .lexer
          | _ => throw .unexpected
  | tokens => do
      let (group, remainder) ← parseGroupPath keywords tokens
      pure (.group group, remainder)

/-- Why a group argument is refused before any group is looked up: a lexical or syntax fault, or a
retired terminal, which the Kernel recognizes and refuses on its own class. -/
inductive MessageGroupArgumentRefusal where
  | syntax (fault : MessageParameterFault)
  | retired (terminal : String)
  deriving Repr, DecidableEq

/-- Decode one group-position argument's tokens, after the `#`, into its alternative and what is
left after the part whose check runs first. The parser meets each token in order, so a lexer fault
answers where it stands and a syntax fault answers before any later token. The token right after a
complete alternative is met before that alternative's check, which is why `$#Store%$` draws the lexer
class and `$#RuleGroup%$` draws it ahead of the root-placement gate. A retired terminal's check is its
refusal; a group's walk, lookup and availability follow in `checkMessageGroup`, and the remainder says
which of them a later token or fault waits for. -/
def decodeMessageGroupTokens (keywords : MessageParameterKeywords) (tokens : List ParameterToken) :
    Except MessageGroupArgumentRefusal (AuthoredMessageGroup × MessageGroupRemainder) :=
  match parseGroupArgument keywords tokens with
  | .error fault => .error (.syntax fault)
  | .ok (.retired terminal, _) => .error (.retired terminal)
  | .ok (.group group, remainder) => .ok (group, remainder)

/-- `decodeMessageGroupTokens` over an argument's spelling, with the `#` already stripped. -/
def decodeMessageGroupArgument (keywords : MessageParameterKeywords) (argument : String) :
    Except MessageGroupArgumentRefusal (AuthoredMessageGroup × MessageGroupRemainder) :=
  decodeMessageGroupTokens keywords (ParameterToken.ofParameter keywords argument)

end A12Kernel
