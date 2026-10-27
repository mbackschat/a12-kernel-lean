import A12Kernel.Elaboration.Flat.Types

/-! # A rule message parameter's lexer and its shared entity and key syntax

The Kernel parses each `$…$` parameter on its own, with one grammar for both positions: an entity spec,
which is the rule-group terminal or a path; an optional suffix; and an optional semantic-index key,
which is a literal or an entity spec with its own key. This module forms the tokens that grammar reads
and decodes the parts both positions share. It decides nothing about the model.

The decoders return **events**, the checks and faults in the order the Kernel's parser meets them,
because its checks are actions that run where their grammar rule ends and its error strategy stops at
the first event that fails ([`LF200`](../../docs/LEAN-FINDINGS.md)). Two facts fix that order. The
token stream fetches the next token when it consumes one, so a lexer fault answers before any check
that runs after the token in front of it is consumed. And a decision that must look ahead reads its
whole window before any action inside it runs, which is why a syntax fault directly after an unknown
name in the name position answers before that name's lookup
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)).
-/

namespace A12Kernel

/-- The seven non-ASCII letters `nameOhnePunkt` names (`spec/12` §1). They are the whole non-ASCII
part of the name token, so a name is refused for being *unknown*, never for its umlaut, and the lexer
that rejects `é` must let the same seven through. -/
def messageNameGermanLetters : List Char := "ÄÜÖäüöß".toList

/-- A character a message parameter's name token may carry. -/
def isMessageNameCharacter (character : Char) : Bool :=
  ('a' ≤ character && character ≤ 'z') ||
    ('A' ≤ character && character ≤ 'Z') ||
    ('0' ≤ character && character ≤ '9') ||
    character == '_' || character == ':' ||
    messageNameGermanLetters.contains character

/-- The selected condition language's words the parameter lexer and grammar distinguish. A word in
`reserved` but not in `exempt` is a keyword and never a name; `ruleGroup`, `rootGroup` and the
`retired` terminals open the group position's keyword alternatives, and the `offset` terminals among
the retired ones take a signed offset. An exempt word may stand inside a dotted name, and may end one
unless it is in `exemptNonFinal`, which is the value suffix and the two form-pointer terminals.
`forTerminal` opens a semantic-index key in either position. The caller supplies the language's
spellings. -/
structure MessageParameterKeywords where
  reserved : List String
  exempt : List String
  exemptNonFinal : List String
  ruleGroup : String
  rootGroup : String
  retired : List String
  offset : List String
  forTerminal : String
  deriving Repr, DecidableEq

/-- Which lexical or syntax class a malformed parameter falls into. The Kernel's error strategy draws
one code per shape, so this fragment reproduces the class; what it does not reproduce is the character
**position** the lexer code additionally carries, which is a payload rather than a class.

Measured at the [group-parameter resolution
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-parameter-resolution) and the [argument-layer
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers): an
unbalanced quote, an empty or digit-first quoted name, and a character such as `[`, `*` or `%` draw
`MVK_LEXER_STANDARD_ERROR`, a trailing separator `MVK_INCOMPLETE_INPUT`, and a doubled separator or a
token left after a path `MVK_UNEXPECTED_TOKEN`. The trailing and doubled separators are the pair that
shows the empty segment's **position** decides. -/
inductive MessageParameterFault where
  /-- A character the parameter lexer forms no token from, a quoted name's first character among
  them. `MVK_LEXER_STANDARD_ERROR`. -/
  | lexer
  /-- The text ends where a choice still needs a token. `MVK_INCOMPLETE_INPUT`. -/
  | truncated
  /-- The text ends where one specific token is required: a signed offset's digits, or the `..` a run
  of two or more up-steps ending on its separator still requires. `MVK_EXPECTED_TOKEN_NOT_FOUND`, the
  class `spec/12` §3.1 gives a failed required match at the end of the text, where a failed choice
  there is `truncated`. -/
  | expectedToken
  /-- An empty non-final segment: two separators with nothing between them. `MVK_UNEXPECTED_TOKEN`. -/
  | separator
  /-- A token no alternative continues, or one left after a complete parameter.
  `MVK_UNEXPECTED_TOKEN`. -/
  | unexpected
  deriving Repr, DecidableEq

/-- One token of a parameter as the parameter grammar's lexer forms it, whitespace dropped as the lexer
hides it. A quoted name is a name with its quotes erased, and `quoted` keeps whether it could still be
read as a keyword. An unquoted reserved word outside the exempt set is a `keyword`, which no name
position accepts. A run of digits is a `number`, which the path grammar takes as a name and a signed
offset as its digits. A name continued by dotted words is one `dotted` token, its `first` word beside
the whole `text`. A string literal keeps its text with the `""` escape undone. `bad` stands where the
lexer forms no token, and ends the list. -/
inductive ParameterToken where
  | name (text : String) (quoted : Bool)
  | keyword (text : String)
  | number (digits : String)
  | dotted (first text : String)
  | literal (text : String)
  | slash
  | up
  | dot
  | sign (negative : Bool)
  | arrow
  | hash
  | openParenthesis
  | closeParenthesis
  | bad
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

/-- A string literal's text, with `""` as its escape, beside what follows its closing quote, or `none`
when it is unclosed. -/
private def stringLiteral : List Char → Option (List Char × List Char)
  | '"' :: '"' :: rest => (stringLiteral rest).map fun (text, after) => ('"' :: text, after)
  | '"' :: rest => some ([], rest)
  | character :: rest => (stringLiteral rest).map fun (text, after) => (character :: text, after)
  | [] => none

/-- Tokenize a parameter up to its first lexer fault, which ends the list as `bad`: the parser meets
that fault when it reaches the token, so nothing after it can answer first. The token set is read from
the Kernel's parameter lexer, and the rows the [argument-layer
checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers) and the
[token-alphabet checkpoint](../../docs/sources/message-and-pointer-probes.md#src-parameter-token-versus-group-declaration-alphabet)
measure agree with it: a quoted name must open on a letter, the longest run of name characters is one
token, so `1x` is a digit-initial name while `1` alone is a number, and `-`, `+`, `(`, `)`, `.` and
whitespace form tokens while `[`, `*`, `%` and a letter outside the seven German ones do not. A word is
a keyword exactly when it is reserved and not exempt from quoting, so `RuleGroup`, `For` and `BaseYear`
are keywords in English while `RootGroup`, `Zeile`, `Usb`, `index` and `value` are names, which the
[argument-event checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-events)
measures in both directions. `fuel` bounds the walk, since every step consumes a character. -/
def tokenizeParameter (keywords : MessageParameterKeywords) :
    Nat → List Char → List ParameterToken
  | 0, _ => [.bad]
  | _ + 1, [] => []
  | fuel + 1, character :: rest =>
      if character == ' ' || character == '\t' || character == '\r' || character == '\n' ||
          character == '\x0C' then
        tokenizeParameter keywords fuel rest
      else if character == '/' then
        .slash :: tokenizeParameter keywords fuel rest
      else if character == '.' then
        match rest with
        | '.' :: after => .up :: tokenizeParameter keywords fuel after
        | _ => .dot :: tokenizeParameter keywords fuel rest
      else if character == '\'' then
        match spanNameCharacters rest with
        | (first :: body, '\'' :: after) =>
            if isNameStartCharacter first then
              .name (String.ofList (first :: body)) true :: tokenizeParameter keywords fuel after
            else [.bad]
        | _ => [.bad]
      else if character == '"' then
        match stringLiteral rest with
        | some (text, after) => .literal (String.ofList text) :: tokenizeParameter keywords fuel after
        | none => [.bad]
      else if character == '-' then
        match rest with
        | '>' :: after => .arrow :: tokenizeParameter keywords fuel after
        | _ => .sign true :: tokenizeParameter keywords fuel rest
      else if character == '+' then
        .sign false :: tokenizeParameter keywords fuel rest
      else if character == '#' then
        .hash :: tokenizeParameter keywords fuel rest
      else if character == '(' then
        .openParenthesis :: tokenizeParameter keywords fuel rest
      else if character == ')' then
        .closeParenthesis :: tokenizeParameter keywords fuel rest
      else if isMessageNameCharacter character then
        let (run, after) := spanNameCharacters rest
        let text := String.ofList (character :: run)
        let token :=
          if (character :: run).all Char.isDigit then .number text
          else if keywords.reserved.contains text && !keywords.exempt.contains text then
            .keyword text
          else .name text false
        token :: tokenizeParameter keywords fuel after
      else [.bad]

/-- Whether a token may follow a dot inside a name, beside whether it may also end that name. A quoted
name and a letter-initial name may do both; an exempt word may continue a name and end it unless it is
in `exemptNonFinal`. A number, a digit-initial name and a keyword continue none. -/
def dottedContinuation? (keywords : MessageParameterKeywords) :
    ParameterToken → Option (String × Bool)
  | .name text true => some (text, true)
  | .name text false =>
      if text.front.isDigit then none
      else if keywords.exempt.contains text then some (text, !keywords.exemptNonFinal.contains text)
      else some (text, true)
  | _ => none

/-- The longest dotted continuation of a name whose last word may end it, beside the tokens after it.
That is the parameter grammar's name rule: dotted words, an exempt word allowed inside, and a narrower
set allowed last, so `$#Head.value$` leaves `.value` after the name while `$#Head.value.x$` is one
name ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)). -/
private def takeDottedContinuation (keywords : MessageParameterKeywords) :
    List ParameterToken → List String × List ParameterToken
  | .dot :: token :: rest =>
      match dottedContinuation? keywords token with
      | some (text, mayEnd) =>
          match takeDottedContinuation keywords rest with
          | ([], _) => if mayEnd then ([text], rest) else ([], .dot :: token :: rest)
          | (more, after) => (text :: more, after)
      | none => ([], .dot :: token :: rest)
  | tokens => ([], tokens)

/-- Join every name with its dotted continuation into one `dotted` token. A signed offset's digits
are no name, so a dot after them is left for the parser, which meets it after the offset alternative
is complete. Deciding whether a name continues past a dot reads the token after the dot, so a lexer
fault there ends the list right after the name and answers before any check the name waits for:
`$#Store.%$` draws the lexer class, `$#Zeile-1.x$` the retired one
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-group-walk-and-dotted-names)).
A category name after an arrow is one token with no continuation, so nothing past a dot after it is
read: `$Grade->Nope.%$` draws the category class
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)).
`fuel` bounds the walk, since every step consumes a token. -/
def joinDottedNames (keywords : MessageParameterKeywords) :
    Nat → List ParameterToken → List ParameterToken
  | 0, tokens => tokens
  | _ + 1, [] => []
  | fuel + 1, .sign negative :: .number digits :: rest =>
      .sign negative :: .number digits :: joinDottedNames keywords fuel rest
  | fuel + 1, .arrow :: token :: rest => .arrow :: token :: joinDottedNames keywords fuel rest
  | fuel + 1, token :: rest =>
      let joined (first : String) :=
        let (name, after) :=
          match takeDottedContinuation keywords rest with
          | ([], _) => (token, rest)
          | (more, after) => (.dotted first (".".intercalate (first :: more)), after)
        match after with
        | .dot :: .bad :: _ => [name, .bad]
        | _ => name :: joinDottedNames keywords fuel after
      match token with
      | .name text _ => joined text
      | .number text => joined text
      | _ => token :: joinDottedNames keywords fuel rest

/-- The tokens of one parameter body, names joined with their dotted continuations. -/
def ParameterToken.ofParameter (keywords : MessageParameterKeywords) (parameter : String) :
    List ParameterToken :=
  let tokens := tokenizeParameter keywords (parameter.length + 1) parameter.toList
  joinDottedNames keywords tokens.length tokens

/-- A token's reading as a name: its first word, which is all a turning point compares, beside the
segment it names. -/
def ParameterToken.name? : ParameterToken → Option (String × String)
  | .name text _ | .number text => some (text, text)
  | .dotted first text => some (first, text)
  | _ => none

/-- A token's reading as one path segment, keeping whether it was quoted. -/
private def ParameterToken.segment? : ParameterToken → Option AuthoredPathName
  | .name text quoted => some { text, quoted }
  | .number text => some { text }
  | .dotted _ text => some { text }
  | _ => none

/-- The class of a fault met at the head of `tokens`, when the parser needs a token there and this one
continues nothing: the end of the text, a lexer fault, or any other token. -/
def MessageParameterFault.at : List ParameterToken → MessageParameterFault
  | [] => .truncated
  | .bad :: _ => .lexer
  | _ => .unexpected

/-- An entity spec as authored: the rule-group terminal, a parent walk naming no segment after it, or
a path. -/
inductive MessageEntitySpec where
  | ruleGroup
  | walk (parents : Nat) (turningPoint : Option AuthoredPathName)
  | path (path : AuthoredFieldPath)
  deriving Repr, DecidableEq

/-- Build an entity spec from its base, turning point and segments. -/
private def MessageEntitySpec.ofSegments (base : PathBase) (turningPoint : Option AuthoredPathName) :
    List AuthoredPathName → Option MessageEntitySpec
  | [] =>
      match base with
      | .relative (parents + 1) => some (.walk (parents + 1) turningPoint)
      | _ => none
  | first :: rest =>
      let field := (first :: rest).getLast (List.cons_ne_nil _ _)
      some (.path { base, turningPoint, groups := (first :: rest).dropLast, field })

/-- The segments after a separator, each separator demanding one, beside the tokens after them. A name
followed by a lexer fault is not yet complete, since the fault answers when the name is consumed, so it
stays out of the segments read before the fault. -/
private def parseSegmentsAfterSlash :
    List ParameterToken →
      Except (List AuthoredPathName × MessageParameterFault)
        (List AuthoredPathName × List ParameterToken)
  | token :: rest =>
      match token.segment?, rest with
      | some _, .bad :: _ => .error ([], .lexer)
      | some segment, .slash :: more =>
          match parseSegmentsAfterSlash more with
          | .ok (segments, after) => .ok (segment :: segments, after)
          | .error (read, fault) => .error (segment :: read, fault)
      | some segment, after => .ok ([segment], after)
      | none, _ =>
          .error ([], match token with | .slash => .separator | _ => MessageParameterFault.at [token])
  | [] => .error ([], .truncated)

/-- The up-run of a relative entity spec after its first `..`: further `../` steps, then a turning
point written directly after the last step, then segments after a separator. Returns the number of
parents, the turning point and the tokens after them. A turning point is compared by its first word
alone, in this position as in the group position, so `$..Probe.x$` names `Probe`. -/
private def parseUpRun (parents : Nat) :
    List ParameterToken → Nat × Option AuthoredPathName × List ParameterToken
  | .slash :: .up :: rest => parseUpRun (parents + 1) rest
  | .dotted first _ :: rest => (parents, some { text := first }, rest)
  | token :: rest =>
      match token.segment? with
      | some turningPoint => (parents, some turningPoint, rest)
      | none => (parents, none, token :: rest)
  | [] => (parents, none, [])

/-- Decode one entity spec in place, as an in-rule parse meets it. The spec's two grammar alternatives
share their path syntax, so the parser's choice between them reads a spec opening on a name or a
separator to its end before any of its names is looked up, and a fault inside it returns no names. A
spec opening on a parent walk has no such choice: the parser looks each completed name up before it
consumes the next token, so a fault returns the spec its names read so far, `$Score For ../Nope/$`
drawing the entity class where `$Score For Nope/$` draws the truncated one
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). -/
def parseMessageEntitySpec (keywords : MessageParameterKeywords) :
    List ParameterToken →
      Except (Option MessageEntitySpec × MessageParameterFault)
        (MessageEntitySpec × List ParameterToken)
  | .keyword word :: rest =>
      if word == keywords.ruleGroup then
        match rest with
        | .bad :: _ => .error (none, .lexer)
        | _ => .ok (.ruleGroup, rest)
      else .error (none, .unexpected)
  | .slash :: rest =>
      match parseSegmentsAfterSlash rest with
      | .ok (segments, after) =>
          match MessageEntitySpec.ofSegments .absolute none segments with
          | some spec => .ok (spec, after)
          | none => .error (none, .truncated)
      | .error (_, fault) => .error (none, fault)
  | .up :: rest =>
      let (parents, turningPoint, after) := parseUpRun 1 rest
      let walk := MessageEntitySpec.walk parents turningPoint
      match after with
      | .bad :: _ => .error (none, .lexer)
      | .slash :: more =>
          match parseSegmentsAfterSlash more with
          | .ok (segments, left) =>
              match MessageEntitySpec.ofSegments (.relative parents) turningPoint segments with
              | some spec => .ok (spec, left)
              | none => .ok (walk, left)
          | .error (read, fault) =>
              .error ((MessageEntitySpec.ofSegments (.relative parents) turningPoint read).orElse
                fun _ => some walk, fault)
      | left => .ok (walk, left)
  | tokens =>
      match parseSegmentsAfterSlash tokens with
      | .ok (segments, after) =>
          match MessageEntitySpec.ofSegments (.relative 0) none segments with
          | some spec => .ok (spec, after)
          | none => .error (none, .truncated)
      | .error (_, fault) => .error (none, fault)

/-- One check or fault in the order the parser meets it. -/
inductive MessageParameterEvent where
  /-- An entity spec's names end and the parser resolves them. -/
  | resolve (entity : MessageEntitySpec)
  /-- A key's own key ends and is refused, `ILLEGAL_SEMANTIC_INDEX`. -/
  | nestedKey
  /-- A lexer or syntax fault; nothing after it runs. -/
  | fault (fault : MessageParameterFault)
  deriving Repr, DecidableEq

/-- The outermost key as authored: a literal, or an entity spec. -/
inductive MessageKeyHead where
  | literal (text : String)
  | entity (entity : MessageEntitySpec)
  deriving Repr, DecidableEq

/-- Decode a semantic-index key after its `For`, the grammar's recursive key: a literal, or an entity
spec with an optional key of its own. A literal takes no key, so a `For` after one is left for the
caller as a token after the parameter. A key's own key is refused when that inner key ends, innermost
first and after every name in it resolves ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-name-position-carriers)),
so a keyed key returns the events up to that refusal. Returns the events, then the head and the tokens
after the key when no event refused it. `fuel` bounds the recursion. -/
def decodeMessageKey (keywords : MessageParameterKeywords) :
    Nat → List ParameterToken →
      List MessageParameterEvent × Option (MessageKeyHead × List ParameterToken)
  | 0, _ => ([.fault .unexpected], none)
  | _ + 1, .literal text :: rest =>
      match rest with
      | .bad :: _ => ([.fault .lexer], none)
      | _ => ([], some (.literal text, rest))
  | fuel + 1, tokens =>
      match parseMessageEntitySpec keywords tokens with
      | .error (read, fault) => (read.toList.map .resolve ++ [.fault fault], none)
      | .ok (entity, rest) =>
          let resolved := MessageParameterEvent.resolve entity
          match rest with
          | .keyword word :: inner =>
              if word == keywords.forTerminal then
                match decodeMessageKey keywords fuel inner with
                | (events, none) => (resolved :: events, none)
                | (events, some (_, .bad :: _)) => (resolved :: events ++ [.fault .lexer], none)
                | (events, some _) => (resolved :: events ++ [.nestedKey], none)
              else ([resolved], some (.entity entity, rest))
          | _ => ([resolved], some (.entity entity, rest))

/-- The selected language's terminals the name position reads beyond the shared keywords. -/
structure MessageNameTerminals where
  baseYear : String
  valueSuffix : String
  formLine : String
  formName : String
  deriving Repr, DecidableEq

/-- What a name-position field carries after its entity spec. A category name is one token. -/
inductive MessageFieldSuffix where
  | none
  | value
  | category (name : String)
  deriving Repr, DecidableEq

/-- Which form-pointer terminal a parameter ends on. -/
inductive MessageFormPointer where
  | line
  | name
  deriving Repr, DecidableEq

/-- The name-position alternative the parser chose, whose own check runs where its rule ends. -/
inductive MessageNameForm where
  | field (entity : MessageEntitySpec) (suffix : MessageFieldSuffix)
      (key : Option MessageKeyHead)
  | formPointer (entity : MessageEntitySpec) (pointer : MessageFormPointer)
  | baseYear (offset : Int)
  | indexField (entity : MessageEntitySpec) (suffix : MessageFieldSuffix)
  deriving Repr, DecidableEq

/-- A decoded name-position parameter: the events before the form's check, the form when no event
ended the parse, and a fault the parser meets after that check, at the end it requires. -/
structure DecodedMessageName where
  events : List MessageParameterEvent
  form : Option MessageNameForm
  trailing : Option MessageParameterFault := none
  deriving Repr, DecidableEq

/-- A fault the parser meets where it tries to continue a dotted name and cannot. -/
private def continuationFault (keywords : MessageParameterKeywords) :
    List ParameterToken → MessageParameterFault
  | .dot :: token :: rest =>
      if (dottedContinuation? keywords token).isSome then continuationFault keywords rest
      else MessageParameterFault.at [token]
  | .dot :: [] => .truncated
  | tokens => MessageParameterFault.at tokens

private def refusedName (fault : MessageParameterFault) : DecodedMessageName :=
  { events := [.fault fault], form := none }

/-- The rest of a field after its entity spec and suffix: its key, then the end of the text. -/
private def decodeFieldTail (keywords : MessageParameterKeywords) (entity : MessageEntitySpec)
    (suffix : MessageFieldSuffix) : List ParameterToken → DecodedMessageName
  | [] => { events := [.resolve entity], form := some (.field entity suffix none) }
  | .bad :: _ => { events := [.resolve entity, .fault .lexer], form := none }
  | .keyword word :: after =>
      if word == keywords.forTerminal then
        match decodeMessageKey keywords (after.length + 1) after with
        | (events, none) => { events := .resolve entity :: events, form := none }
        | (events, some (key, rest)) =>
            { events := .resolve entity :: events, form := some (.field entity suffix (some key))
              trailing := if rest.isEmpty then none else some .unexpected }
      else
        { events := [.resolve entity], form := some (.field entity suffix none),
          trailing := some .unexpected }
  | _ =>
      { events := [.resolve entity], form := some (.field entity suffix none),
        trailing := some .unexpected }

/-- Decode a name-position parameter whose first token is no `#`.

The Base Year terminal opens its own alternative at once, so its signed offset and the end of the text
answer in place around its check. Every other alternative begins with the same entity spec, so the
parser's decision reads the whole spec and the token or two after it before any check runs, and a
fault inside that window answers first: `$Nope x$`, `$Nope/$` and `$Nope.Vordruckzeile x$` draw the
syntax class where `$Nope For$` and `$Nope->Band x$` draw the entity's. The window ends at the end of
the text, an arrow, a key, or a value suffix followed by either, and on a form-pointer terminal
followed by the end of the text; a dotted continuation that fails after a value or pointer terminal
is still inside it. After the window the field's suffix, then its key, then its own check, and only
then the end of the text answer in that order
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-decoder)). -/
def decodeMessageName (keywords : MessageParameterKeywords) (terminals : MessageNameTerminals) :
    List ParameterToken → DecodedMessageName
  | .keyword word :: rest =>
      if word == terminals.baseYear then
        let finish (offset : Int) (after : List ParameterToken) : DecodedMessageName :=
          match after with
          | .bad :: _ => refusedName .lexer
          | [] => { events := [], form := some (.baseYear offset) }
          | _ => { events := [], form := some (.baseYear offset), trailing := some .unexpected }
        match rest with
        | .sign negative :: .number digits :: after =>
            let magnitude := Int.ofNat digits.toNat!
            finish (if negative then -magnitude else magnitude) after
        | .sign _ :: after =>
            match after with
            | [] => refusedName .expectedToken
            | .bad :: _ => refusedName .lexer
            | _ => refusedName .unexpected
        | after => finish 0 after
      else if word == keywords.ruleGroup then decodeNameAfterEntity .ruleGroup rest
      else refusedName (MessageParameterFault.at [.keyword word])
  | tokens =>
      match parseMessageEntitySpec keywords tokens with
      | .error (_, fault) =>
          refusedName (if fault == .expectedToken then .truncated else fault)
      | .ok (entity, rest) => decodeNameAfterEntity entity rest
where
  decodeNameAfterEntity (entity : MessageEntitySpec) : List ParameterToken → DecodedMessageName
    | .arrow :: after =>
        match after with
        | .bad :: _ => { events := [.resolve entity, .fault .lexer], form := none }
        | token :: rest =>
            match token.name? with
            | some (name, _) => decodeFieldTail keywords entity (.category name) rest
            | none => decodeFieldTail keywords entity (.category "") (token :: rest)
        | [] => decodeFieldTail keywords entity (.category "") []
    | .dot :: .name word false :: after =>
        if word == terminals.valueSuffix then
          match after with
          | [] => decodeFieldTail keywords entity .value []
          | .keyword key :: _ =>
              if key == keywords.forTerminal then decodeFieldTail keywords entity .value after
              else refusedName .unexpected
          | _ => refusedName (continuationFault keywords after)
        else if word == terminals.formLine || word == terminals.formName then
          let pointer := if word == terminals.formLine then MessageFormPointer.line else .name
          match after with
          | [] => { events := [.resolve entity], form := some (.formPointer entity pointer) }
          | _ => refusedName (continuationFault keywords after)
        else refusedName (continuationFault keywords (.dot :: .name word false :: after))
    | .openParenthesis :: after =>
        if entity == .path { base := .relative 0, groups := [], field := { text := "index" } } then
          decodeIndex after
        else refusedName .unexpected
    | [] => decodeFieldTail keywords entity .none []
    | .keyword word :: rest =>
        if word == keywords.forTerminal then decodeFieldTail keywords entity .none (.keyword word :: rest)
        else refusedName .unexpected
    | tokens => refusedName (continuationFault keywords tokens)
  decodeIndex (tokens : List ParameterToken) : DecodedMessageName :=
    match parseMessageEntitySpec keywords tokens with
    | .error (_, fault) => refusedName fault
    | .ok (entity, .closeParenthesis :: after) =>
        match after with
        | [] => { events := [], form := some (.indexField entity .none) }
        -- After the closing parenthesis the grammar takes the suffix keyword alone, not a dotted
        -- name, so any other word there is an unexpected token: the other language's suffix and a
        -- capitalised one alike ([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-index-german-suffix)).
        | .dot :: .name word false :: rest =>
            if word == terminals.valueSuffix then finishIndex entity .value rest
            else refusedName .unexpected
        | .arrow :: token :: rest =>
            match token.name? with
            | some (name, _) => finishIndex entity (.category name) rest
            | none => refusedName (MessageParameterFault.at (token :: rest))
        | .arrow :: [] => finishIndex entity (.category "") []
        | .bad :: _ => refusedName .lexer
        | rest => finishIndex entity .none rest
    | .ok (_, rest) => refusedName (MessageParameterFault.at rest)
  finishIndex (entity : MessageEntitySpec) (suffix : MessageFieldSuffix)
      (rest : List ParameterToken) : DecodedMessageName :=
    match rest with
    | .bad :: _ => refusedName .lexer
    | [] => { events := [], form := some (.indexField entity suffix) }
    | _ => { events := [], form := some (.indexField entity suffix), trailing := some .unexpected }

end A12Kernel
