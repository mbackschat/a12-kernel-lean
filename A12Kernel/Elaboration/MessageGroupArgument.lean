import A12Kernel.Elaboration.Flat.Types

/-! # The message group position's argument syntax

A rule message's `$#…$` parameter takes a group argument, and this module decodes its spelling: the
tokens the parameter lexer forms, the alternative the parameter grammar chooses, and the lexical or
syntax class of the first token no alternative continues. It decides nothing about the model. Which
group an authored argument names, whether that group is available to the message, and when a token
left after it is refused belong to `checkMessageGroup` in `ValidationMessageAuthoring`, which consumes
this decoder.

The classes follow the order in which the Kernel's parser meets the argument, measured at the
[argument-event checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events).
-/

namespace A12Kernel

/-- The seven non-ASCII letters `nameOhnePunkt` names (`spec/11` Part B). They are the whole non-ASCII
part of both the parameter body's lexical bound and the name token itself, so the predicates that need
them share the set rather than each spelling it: a name is refused for being *unknown*, never for its
umlaut, and the lexer that rejects `é` must let the same seven through. -/
def messageNameGermanLetters : List Char := "ÄÜÖäüöß".toList

/-- A character a message parameter's name token may carry. -/
def isMessageNameCharacter (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') ||
    ('A' ≤ character && character ≤ 'Z') ||
    ('0' ≤ character && character ≤ '9') ||
    character == '_' || character == ':' ||
    messageNameGermanLetters.contains character

/-- The selected condition language's words the group argument's lexer and grammar distinguish. A
word in `reserved` but not in `exempt` is a keyword and never a name; `ruleGroup`, `rootGroup` and the
`retired` terminals open the group position's keyword alternatives, and the `offset` terminals among
the retired ones take a signed offset. The caller supplies the language's spellings. -/
structure MessageGroupKeywords where
  reserved : List String
  exempt : List String
  ruleGroup : String
  rootGroup : String
  retired : List String
  offset : List String
  deriving Repr, DecidableEq

/-- Which lexical or syntax class a malformed group argument falls into. The Kernel reports three
distinct codes among these shapes rather than one parse class, and the class follows the malformed
shape, so this fragment reproduces it. What it does not reproduce is the character **position** the
lexer code additionally carries, which is a payload rather than a class.

Measured at the [group-parameter resolution
checkpoint](../../docs/SOURCES.md#src-message-group-parameter-resolution) and the [argument-layer
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers): an
unbalanced quote, an empty or digit-first quoted name, and a character such as `[`, `*` or `%` draw
`MVK_LEXER_STANDARD_ERROR`, a trailing separator `MVK_INCOMPLETE_INPUT`, and a doubled separator or a
token left after a path `MVK_UNEXPECTED_TOKEN`. The trailing and doubled separators are the pair that
shows the empty segment's **position** decides. -/
inductive MessageGroupLexicalFault where
  /-- A character the parameter lexer forms no token from, a quoted name's first character among
  them. `MVK_LEXER_STANDARD_ERROR`. -/
  | lexer
  /-- An empty final segment: the argument ends on its separator. `MVK_INCOMPLETE_INPUT`. -/
  | truncated
  /-- The argument ends where one specific token is required: a retired terminal's offset sign with no
  digits after it. `MVK_EXPECTED_TOKEN_NOT_FOUND`, the class `spec/12` §3.1 gives a failed required
  match at the end of the text, where a failed choice there is `truncated`. -/
  | expectedToken
  /-- An empty non-final segment: two separators with nothing between them. `MVK_UNEXPECTED_TOKEN`. -/
  | separator
  /-- A token where a separator must be followed by a name, or one left after a complete path.
  `MVK_UNEXPECTED_TOKEN`. A token left after a path is reported only once the path resolves to an
  available group. -/
  | unexpected
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

/-- One token of a group argument as the parameter grammar's lexer forms it, whitespace dropped as the
lexer hides it. A quoted name is a name with its quotes erased, and `quoted` keeps whether it could
still be read as a keyword. An unquoted reserved word outside the exempt set is a `keyword`, which no
name position accepts. A run of digits is a `number`, which the path grammar takes as a name and a
retired terminal's offset as its digits. `bad` stands where the lexer forms no token. Every other token
the path grammar has no use for is `other`. -/
private inductive GroupToken where
  | name (text : String) (quoted : Bool)
  | keyword (text : String)
  | number (digits : String)
  | slash
  | up
  | sign
  | bad
  | other
  deriving Repr, DecidableEq

private def isNameStartCharacter (character : Char) : Bool :=
  isMessageNameCharacter character && !character.isDigit

/-- The longest run of name characters, beside what follows it. -/
private def spanNameCharacters : List Char → List Char × List Char
  | character :: rest =>
      if isMessageNameCharacter character then
        let (run, after) := spanNameCharacters rest
        (character :: run, after)
      else ([], character :: rest)
  | [] => ([], [])

/-- What follows a string literal's closing quote, with `""` as its escape, or `none` when unclosed. -/
private def afterStringLiteral : List Char → Option (List Char)
  | '"' :: '"' :: rest => afterStringLiteral rest
  | '"' :: rest => some rest
  | _ :: rest => afterStringLiteral rest
  | [] => none

/-- Tokenize a group argument up to its first lexer fault, which ends the list as `bad`: the parser
meets that fault when it reaches the token, so nothing after it can answer first. The token set is
read from the Kernel's parameter lexer, and the rows the [argument-layer
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers) and the
[token-alphabet checkpoint](../../docs/SOURCES.md#src-parameter-token-versus-group-declaration-alphabet)
measure agree with it: a quoted name must open on a letter, the longest run of name characters is one
token, so `1x` is a digit-initial name while `1` alone is a number, and `-`, `+`, `(`, `)` and
whitespace form tokens while `[`, `*` and `%` do not. A word is a keyword exactly when it is reserved
and not exempt from quoting, so `RuleGroup`, `For` and `BaseYear` are keywords in English while
`RootGroup`, `Zeile`, `Usb`, `index` and `value` are names, which the [argument-event
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events) measures
in both directions. `fuel` bounds the walk, since every step consumes a character. -/
private def tokenizeGroupArgument (keywords : MessageGroupKeywords) :
    Nat → List Char → List GroupToken
  | 0, _ => [.bad]
  | _ + 1, [] => []
  | fuel + 1, character :: rest =>
      if character == ' ' || character == '\t' || character == '\r' || character == '\n' ||
          character == '\x0C' then
        tokenizeGroupArgument keywords fuel rest
      else if character == '/' then
        .slash :: tokenizeGroupArgument keywords fuel rest
      else if character == '.' then
        match rest with
        | '.' :: after => .up :: tokenizeGroupArgument keywords fuel after
        | _ => .other :: tokenizeGroupArgument keywords fuel rest
      else if character == '\'' then
        match spanNameCharacters rest with
        | (first :: body, '\'' :: after) =>
            if isNameStartCharacter first then
              .name (String.ofList (first :: body)) true :: tokenizeGroupArgument keywords fuel after
            else [.bad]
        | _ => [.bad]
      else if character == '"' then
        match afterStringLiteral rest with
        | some after => .other :: tokenizeGroupArgument keywords fuel after
        | none => [.bad]
      else if character == '-' then
        match rest with
        | '>' :: after => .other :: tokenizeGroupArgument keywords fuel after
        | _ => .sign :: tokenizeGroupArgument keywords fuel rest
      else if character == '+' then
        .sign :: tokenizeGroupArgument keywords fuel rest
      else if character == '(' || character == ')' || character == '#' then
        .other :: tokenizeGroupArgument keywords fuel rest
      else if isMessageNameCharacter character then
        let (run, after) := spanNameCharacters rest
        let text := String.ofList (character :: run)
        let token :=
          if (character :: run).all Char.isDigit then .number text
          else if keywords.reserved.contains text && !keywords.exempt.contains text then
            .keyword text
          else .name text false
        token :: tokenizeGroupArgument keywords fuel after
      else [.bad]

/-- Names after a separator, each separator demanding a name, beside the tokens left after the path.
A digit run is a name here. The token after the last name is left for the caller, which meets a lexer
fault there before running any check. -/
private def parseGroupNamesAfterSlash :
    List GroupToken → Except MessageGroupLexicalFault (List String × List GroupToken)
  | .name name _ :: .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (name :: names, left)
  | .number name :: .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (name :: names, left)
  | .name name _ :: left => pure ([name], left)
  | .number name :: left => pure ([name], left)
  | [] => throw .truncated
  | .bad :: _ => throw .lexer
  | .slash :: _ => throw .separator
  | _ => throw .unexpected

/-- The rest of a relative path after `parents` up-steps: another up-step after a separator, a turning
point written directly after the last up-step, then names after a separator. -/
private def parseGroupUpRun (parents : Nat) :
    List GroupToken → Except MessageGroupLexicalFault (AuthoredMessageGroup × List GroupToken)
  | .slash :: .up :: rest => parseGroupUpRun (parents + 1) rest
  | .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (.relative parents none names, left)
  | .name turningPoint _ :: .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (.relative parents (some turningPoint) names, left)
  | .number turningPoint :: .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (.relative parents (some turningPoint) names, left)
  | .name turningPoint _ :: left => pure (.relative parents (some turningPoint) [], left)
  | .number turningPoint :: left => pure (.relative parents (some turningPoint) [], left)
  | left => pure (.relative parents none [], left)

/-- Parse a tokenized group path into its authored form and the tokens left after it. -/
private def parseGroupPath :
    List GroupToken → Except MessageGroupLexicalFault (AuthoredMessageGroup × List GroupToken)
  | .slash :: rest => do
      let (names, left) ← parseGroupNamesAfterSlash rest
      pure (.absolute names, left)
  | .up :: rest => parseGroupUpRun 1 rest
  | tokens => do
      let (names, left) ← parseGroupNamesAfterSlash tokens
      pure (.relative 0 none names, left)

/-- A group argument's alternative: a group, by keyword or path, or a retired terminal, which the
Kernel recognizes in order to refuse it. -/
private inductive ParsedGroupArgument where
  | group (authored : AuthoredMessageGroup)
  | retired (terminal : String)

/-- The keyword alternative a word opens, if it is one of the group position's terminals. -/
private def groupKeyword? (keywords : MessageGroupKeywords) (word : String) :
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
keyword at the end of the text, the first segment of a path before a separator, and an offset
terminal's alternative before a sign; before any other token neither reading continues, and that is a
syntax refusal before any check. The Kernel's classes on each branch are measured at the [argument-event
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events). -/
private def parseGroupArgument (keywords : MessageGroupKeywords) :
    List GroupToken → Except MessageGroupLexicalFault (ParsedGroupArgument × List GroupToken)
  | [] => throw .truncated
  | .bad :: _ => throw .lexer
  | .keyword word :: rest =>
      match groupKeyword? keywords word with
      | some keyword => pure (keyword, rest)
      | none => throw .unexpected
  | .name word false :: rest =>
      let path := do
        let (group, left) ← parseGroupPath (.name word false :: rest)
        pure (ParsedGroupArgument.group group, left)
      match groupKeyword? keywords word with
      | none => path
      | some keyword =>
          match rest with
          | [] => pure (keyword, [])
          | .slash :: _ => path
          | .sign :: after =>
              if keywords.offset.contains word then
                match after with
                | .number _ :: left => pure (keyword, left)
                | [] => throw .expectedToken
                | .bad :: _ => throw .lexer
                | _ => throw .unexpected
              else throw .unexpected
          | .bad :: _ => throw .lexer
          | _ => throw .unexpected
  | tokens => do
      let (group, left) ← parseGroupPath tokens
      pure (.group group, left)

/-- Why a group argument is refused before any group is looked up: a lexical or syntax fault, or a
retired terminal, which the Kernel recognizes and refuses on its own class. -/
inductive MessageGroupArgumentRefusal where
  | syntax (fault : MessageGroupLexicalFault)
  | retired (terminal : String)
  deriving Repr, DecidableEq

/-- Decode one group-position argument, with the `#` already stripped, into its alternative and whether
a token is left after it. The parser meets each token in order, so a lexer fault answers where it
stands and a syntax fault answers before any later token. The token right after a complete
alternative is met before that alternative's check, which is why `$#Store%$` draws the lexer class
and `$#RuleGroup%$` draws it ahead of the root-placement gate. A retired terminal's check is its
refusal; a group's lookup and availability follow in `checkMessageGroup`, and a token left after a
group that passes them travels as the flag. -/
def decodeMessageGroupArgument (keywords : MessageGroupKeywords) (argument : String) :
    Except MessageGroupArgumentRefusal (AuthoredMessageGroup × Bool) :=
  match parseGroupArgument keywords
      (tokenizeGroupArgument keywords (argument.length + 1) argument.toList) with
  | .error fault => .error (.syntax fault)
  | .ok (_, .bad :: _) => .error (.syntax .lexer)
  | .ok (.retired terminal, _) => .error (.retired terminal)
  | .ok (.group group, left) => .ok (group, !left.isEmpty)

end A12Kernel
