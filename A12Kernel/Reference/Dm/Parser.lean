import A12Kernel.Reference.Dm.Syntax

/-! # The condition and operation grammar

A recursive-descent reading of spec §12.3's grammar into the untyped `Expr` tree. Conditions and
operations share one entry, `parseText`, because a computation's operation and a rule's condition are
written in the same productions and only the consumer decides which it needs.

The grammar enforces the purely syntactic laws: one connective per bracket pair
(`MVK_BRACKET_MISSING`), parentheses around conditions and braces around operations, a sign only on a
number literal, a comment only at a branch boundary or after `+`. Everything typed is left to lowering.
The class a refused text draws follows spec §12.3.1 at the first failing token; the exact raise point
of each check is the static-legality work's, not this reader's.
-/

namespace A12Kernel.Dm

/-- What the parse completed that the Kernel checks as soon as it completes (spec/12 §12.3): a reference
whose path closed, the steps of a path still open, each step a segment the parse read up to its `/`,
a call whose closing parenthesis the parse read, and a whole reference read, its category, key and
filter included. A read inside a key or a filter body is not recorded, since it binds in a scope the
event does not carry. -/
inductive ParseEvent where
  | reference (path : Path)
  | openPath (path : Path)
  | closedCall (call : Expr)
  | read (reference : Reference)
  deriving Repr, BEq

/-- The cursor over the lexemes, and beneath the failure the events completed so far, which survive a
syntax error. -/
private abbrev P := StateT Nat (ReaderT (Array Lexeme) (ExceptT SyntaxError (StateM (Array ParseEvent))))

private def run (grammar : P α) (lexemes : Array Lexeme) : Except SyntaxError α × Array ParseEvent :=
  Id.run (((grammar.run' 0).run lexemes).run.run #[])

private def peek : P (Option Token) := do
  return (← read)[← get]?.map (·.token)

private def peekAt (ahead : Nat) : P (Option Token) := do
  return (← read)[(← get) + ahead]?.map (·.token)

private def advance : P Unit := modify (· + 1)

/-- Fail at the cursor: `atEnd` is the class the end of the text draws there, a real token always
drawing `MVK_UNEXPECTED_TOKEN` (spec §12.3.1). -/
private def failHere (atEnd : SyntaxErrorClass) : P α := do
  let lexemes ← read
  match lexemes[← get]? with
  | some lexeme => throw { errorClass := .unexpectedToken, offset := lexeme.offset }
  | none => throw { errorClass := atEnd, offset := lexemes.back?.map (·.offset) |>.getD 0 }

private def expectSymbol (symbol : String) : P Unit := do
  if (← peek) == some (.symbol symbol) then advance else failHere .expectedTokenNotFound

private def acceptSymbol (symbol : String) : P Bool := do
  if (← peek) == some (.symbol symbol) then advance; return true else return false

private def acceptKeyword (id : String) : P Bool := do
  if (← peek) == some (.keyword id) then advance; return true else return false

private partial def skipComments : P Unit := do
  if (← peek) == some .comment then advance; skipComments

/-- The date-shift operators, whose second argument is an amount. -/
private def shiftOperators : List String :=
  ["AddDays", "AddMonths", "AddYears", "AddHours", "AddMinutes", "AddSeconds"]

/-- The numeric operators whose first argument is a value; `Min` and `Max` take values throughout. -/
private def valueOperators : List String :=
  ["Abs", "Min", "Max", "RoundUp", "RoundDown", "RoundAccounting"]

/-- The scalar membership operators, whose items after the subject form a value list unless an `In`
follows. -/
private def valueListOperators : List String :=
  ["FieldValueIncludedInValueList", "FieldValueNotIncludedInValueList"]

/-- Whether an `In` follows at the current call's own depth before its closing parenthesis. -/
private partial def inFollowsInCall (ahead : Nat := 0) (depth : Nat := 0) : P Bool := do
  match ← peekAt ahead with
  | none => pure false
  | some (.symbol "(") => inFollowsInCall (ahead + 1) (depth + 1)
  | some (.symbol ")") => if depth == 0 then pure false else inFollowsInCall (ahead + 1) (depth - 1)
  | some (.keyword "In") => if depth == 0 then pure true else inFollowsInCall (ahead + 1) depth
  | some _ => inFollowsInCall (ahead + 1) depth

/-- Keywords that never open an operand. -/
private def separatorKeywords : List String :=
  ["And", "Or", "In", "To", "Having", "For", "@From", "@SuppressWarning", "PatternMatched",
   "PatternViolated", "DiffersWithToleranceRange1", "DiffersWithToleranceRange2",
   "DiffersWithToleranceRange5", "DiffersWithToleranceRange10"]

/-- Whether the cursor starts a call argument: it follows a call's `(`, a `,`, or the `In` or `To` of
an argument list, comments aside. Only there may a bare name stand (spec/12 §12.3). A `(` after a
connective or `Having` opens a condition, whose sides are values (static-legality sweep row `P70`). -/
private def startsArgument : P Bool := do
  let before := ((← read).toList.take (← get)).reverse.filter (·.token != .comment)
  return match (before.map (·.token) : List Token) with
    | Token.symbol "(" :: Token.keyword id :: _ => !separatorKeywords.contains id
    | Token.symbol "," :: _ | Token.keyword "In" :: _ | Token.keyword "To" :: _ => true
    | _ => false

private def compareOp? : Option Token → Option CompareOp
  | some (.symbol "==") => some .eq
  | some (.symbol "!=") => some .ne
  | some (.symbol "<") => some .lt
  | some (.symbol "<=") => some .le
  | some (.symbol ">") => some .gt
  | some (.symbol ">=") => some .ge
  | some (.keyword "PatternMatched") => some .patternMatched
  | some (.keyword "PatternViolated") => some .patternViolated
  | some (.keyword "DiffersWithToleranceRange1") => some (.tolerance 1)
  | some (.keyword "DiffersWithToleranceRange2") => some (.tolerance 2)
  | some (.keyword "DiffersWithToleranceRange5") => some (.tolerance 5)
  | some (.keyword "DiffersWithToleranceRange10") => some (.tolerance 10)
  | _ => none

private def segment : P Segment := do
  match ← peek with
  | some (.name name _) => advance; return { name, star := ← acceptSymbol "*" }
  | _ => failHere .expectedTokenNotFound

/-- The segments after `header`'s prefix, each step read up to its `/` recorded as the open path so far.
A `.*` after a segment is a starred step the walk checks before the spelling's own class is raised, so
`NoSuch.*/Items/` draws the name's class and `Items.*/Count` the star's (spec/12 §12.3). Where the class
stands for a `.*` not followed by `/` is unmeasured; it is raised the same way. -/
private partial def segments (header : Path) : P (List Segment) := do
  let first ← segment
  if (← peek) == some (.symbol ".") && (← peekAt 1) == some (.symbol "*") then
    let offset := (← read)[← get]!.offset
    modifyThe (Array ParseEvent)
      (·.push (.openPath { header with segments := header.segments ++ [{ first with star := true }] }))
    throw { errorClass := .pointInA12Model, offset }
  -- A `.` alone leaves the step open, the walk still reading for its `*`, so the reference never
  -- completes and `Items*/NoSuch.` draws the token class (spec/12 §12.3).
  if (← peek) == some (.symbol ".") then failHere .unexpectedToken
  if ← acceptSymbol "/" then
    let header := { header with segments := header.segments ++ [first] }
    modifyThe (Array ParseEvent) (·.push (.openPath header))
    return first :: (← segments header)
  else return [first]

/-- An up-run: each `..` climbs one level, and a name written directly after the last one is its
turning-point label rather than a descent, which needs the `/`. -/
private partial def ups : P (Nat × Option String) := do
  if (← peek) != some (.symbol "..") then return (0, none)
  advance
  match ← peek with
  | some (.symbol "/") =>
      if (← peekAt 1) == some (.symbol "..") then
        advance
        let (count, label) ← ups
        return (count + 1, label)
      else return (1, none)
  | some (.name label _) => advance; return (1, some label)
  | _ => return (1, none)

/-- A path; once it closes, its steps are no longer open. -/
private def path : P Path := do
  let opened := (← getThe (Array ParseEvent)).size
  let correlated ← acceptSymbol "$"
  let absolute ← acceptSymbol "/"
  let (ups, turningPoint) ← if absolute then pure (0, none) else ups
  let header : Path := { correlated, absolute, ups, turningPoint, segments := [] }
  let segments ← if ups == 0 then segments header
    else if ← acceptSymbol "/" then segments header else pure []
  modifyThe (Array ParseEvent) (·.shrink opened)
  return { header with segments }

/-- Run `grammar`, dropping the reads it records whether or not it fails. -/
private def withoutReads (grammar : P α) : P α := do
  let opened := (← getThe (Array ParseEvent)).size
  let drop := fun (events : Array ParseEvent) => events.extract 0 opened ++
    (events.extract opened events.size).filter fun | .read _ => false | _ => true
  tryCatch (do let result ← grammar; modifyThe (Array ParseEvent) drop; pure result)
    fun error => do modifyThe (Array ParseEvent) drop; throw error

mutual
private partial def indexSuffix : P (Option IndexKey) := do
  if ← acceptKeyword "For" then
    match ← peek with
    | some (.string text) => advance; pure (some (.literal text))
    -- A digit-only key is a name, as the grammar's identifiers admit digits (KF532), so it resolves
    -- and draws the entity class (keyed-membership rows `f00`–`f03`, 2026-10-13).
    | some (.number digits) =>
        if digits.isEmpty || !digits.toList.all Char.isDigit then failHere .expectedTokenNotFound
        advance
        let target : Path := { segments := [{ name := digits, star := false }] }
        modifyThe (Array ParseEvent) (·.push (.reference target))
        pure (some (.reference { path := target }))
    | _ => pure (some (.reference (← reference)))
  else pure none

private partial def reference : P Reference := do
  let target ← path
  modifyThe (Array ParseEvent) (·.push (.reference target))
  let category ← if ← acceptSymbol "->" then
      match ← peek with
      | some (.name name _) => advance; pure (some name)
      | _ => failHere .expectedTokenNotFound
    else pure none
  let index ← withoutReads indexSuffix
  let filter ← if ← acceptKeyword "Having" then pure (some (← withoutReads (condition false))) else pure none
  let read : Reference := { path := target, index, category, filter }
  modifyThe (Array ParseEvent) (·.push (.read read))
  return read

/-- A condition: branches joined by one connective (spec §12.3). `comments` admits a comment at each
branch boundary, which an argument list refuses. -/
private partial def condition (comments : Bool) : P Expr := do
  let mut parts := #[← branch comments]
  let mut op : Option LogicOp := none
  repeat
    let next : Option LogicOp := match ← peek with
      | some (.keyword "And") => some .and
      | some (.keyword "Or") => some .or
      | _ => none
    let some connective := next | break
    if op.any (· != connective) then
      throw { errorClass := .bracketMissing, offset := (← read)[← get]!.offset }
    op := some connective
    advance
    parts := parts.push (← branch comments)
  match op with
  | some connective => return .logic connective parts.toList
  | none => return parts[0]!

private partial def branch (comments : Bool) : P Expr := do
  if comments then skipComments
  let left ← arith
  let result ← match compareOp? (← peek) with
    | some op => do advance; pure (Expr.compare op left (← arith))
    | none => pure left
  if comments then skipComments
  return result

private partial def arith : P Expr := do
  let rec loop (left : Expr) : P Expr := do
    match ← peek with
    | some (.symbol "+") => advance; skipComments; loop (.arith .add left (← term))
    | some (.symbol "-") => advance; loop (.arith .sub left (← term))
    | _ => return left
  loop (← term)

private partial def term : P Expr := do
  let rec loop (left : Expr) : P Expr := do
    match ← peek with
    | some (.symbol "*") => advance; loop (.arith .mul left (← power))
    | some (.symbol "/") => advance; loop (.arith .div left (← power))
    | _ => return left
  loop (← power)

/-- Powers chain to the left as written; whether a chained power is legal is a check (spec §5). -/
private partial def power : P Expr := do
  let rec loop (left : Expr) : P Expr := do
    if ← acceptSymbol "^" then loop (.arith .pow left (← atom)) else return left
  loop (← atom)

private partial def atom : P Expr := do
  match ← peek with
  | some (.symbol "-") =>
      advance
      match ← peek with
      | some (.number digits) => advance; return .number ("-" ++ digits)
      | _ => failHere .incompleteInput
  | some (.number digits) => advance; return .number digits
  | some (.string text) => advance; return .string text
  | some (.symbol "[") =>
      advance
      let reference ← reference
      expectSymbol "]"
      return .value reference
  | some (.symbol "{") =>
      advance
      let body ← arith
      expectSymbol "}"
      return .braces body
  | some (.symbol "(") =>
      advance
      let body ← condition true
      expectSymbol ")"
      return .parens body
  | some (.keyword "CustomCondition") =>
      advance
      match ← peek with
      | some (.name name quoted) => advance; return .custom name quoted
      | some (.number name) =>
          if name.toList.all (fun c => '0' ≤ c && c ≤ '9') then advance; return .custom name
          else failHere .expectedTokenNotFound
      | _ => failHere .expectedTokenNotFound
  | some (.keyword "RuleGroup") =>
      let inArgument ← startsArgument
      advance
      -- In an entity slot a star after the rule-context group is its repetition star, refused by
      -- the entity list (static-legality sweep row `R70`).
      if inArgument && (← peek) == some (.symbol "*") then
        advance
        return .constant "RuleGroup*"
      match ← indexSuffix with
      | none => return .constant "RuleGroup"
      | some key =>
          -- The empty relative group path preserves the declaring group (spec/08 §1).
          return .entity { path := { segments := [] }, index := some key }
  | some (.keyword id) =>
      if separatorKeywords.contains id then failHere .incompleteInput
      advance
      if ← acceptSymbol "(" then call id else return .constant id
  | some (.name _ _) | some (.symbol "/") | some (.symbol "..") | some (.symbol "$") =>
      -- A field's value is read only through a bracket, so a bare name elsewhere, a comparison side
      -- or an arithmetic term, is a token defect at the name: nothing after it is read, and the name
      -- is never resolved (spec/12 §12.3; `NoSuchField > 0` draws the token class).
      if !(← startsArgument) then failHere .incompleteInput
      -- A name that is no keyword before `(` is a token defect too, raised before the name is resolved
      -- (predicate-operand capture rows `d01`–`d05`, 2026-10-14).
      if let some (.name _ _) := ← peek then
        if (← peekAt 1) == some (.symbol "(") then failHere .incompleteInput
      return .entity (← reference)
  | _ => failHere .incompleteInput

private partial def call (id : String) : P Expr := do
  let closed ← callBody id
  modifyThe (Array ParseEvent) (·.push (.closedCall closed))
  return closed

private partial def callBody (id : String) : P Expr := do
  -- Only `Time` takes an optional first operand; every other production requires one, so its `)`
  -- right after `(` is a token defect (grammar `timeKonstrukt`; k22-static-classes-2026-10-24,
  -- `s6-slot-empty`).
  if (← peek) == some (.symbol ")") && id != "Time" then failHere .unexpectedToken
  if ← acceptSymbol ")" then return .call id [] none none
  let arguments ← argumentList id
  -- datumParam uses entitySpec; digit-only names are identifiers here (KF532; grammar idName).
  -- Keep invalid shapes for the ordered admission walk, where earlier entity failures still win.
  let arguments := if id == "Date" || id == "Time" then arguments.map (fun
      | .mk (.number digits) none =>
          if !digits.isEmpty && digits.toList.all Char.isDigit then
            .mk (.entity { path := { segments := [{ name := digits, star := false }] } }) none
          else .mk (.number digits) none
      | argument => argument) else arguments
  let listed ← if ← acceptKeyword "In" then pure (some (← argumentList "In")) else pure none
  let scope ← if ← acceptKeyword "@From" then pure (some (← reference)) else pure none
  -- Validity takes a constructed Date or a field and a type name, so a lone field operand meets `)`
  -- where the grammar expects `,` (spec/05; parallel-instance-leaves rows `v17`, `v18`, 2026-10-14),
  -- and a third operand is a token defect too ([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18)).
  if (id == "Valid" || id == "Invalid") && (match arguments with
      | [.mk (.call "Date" _ none none) none] => false
      | [_] | _ :: _ :: _ :: _ => true
      | _ => false) then failHere .expectedTokenNotFound
  expectSymbol ")"
  return .call id arguments listed scope

private partial def argumentList (id : String) (index : Nat := 0) : P (List Argument) := do
  let first ← argument id index
  if ← acceptSymbol "," then return first :: (← argumentList id (index + 1)) else return [first]

private partial def argument (id : String) (index : Nat) : P Argument := do
  -- A date shift's amount is a value, so a bare name there is a token defect like any bare value
  -- (spec/12 §12.3). `AddDays` is measured (static-legality sweep row `R40`); the other shifts share
  -- its production, an assumption no row measures.
  -- The numeric operators' value slots follow the same rule, bare outside a filter body and bare or
  -- marked inside one (handback rows of 2026-10-23, `sv1`–`sv9`, `sa1`–`sa4`, `sb1`–`sb6`,
  -- `sh1`–`sh10`). A bare name and a bracketed read in a rounding operator's digits slot draw the
  -- token class too (`sd1`, `sd2`).
  if index == 1 && shiftOperators.contains id ||
      valueOperators.contains id && (index == 0 || id == "Min" || id == "Max") then
    match ← peek with
    | some (.name _ _) | some (.symbol "/") | some (.symbol "..") | some (.symbol "$") =>
        failHere .incompleteInput
    | _ => pure ()
  -- A value list holds only String and number literals and bracketed field reads, so a bare name or
  -- a keyword constant there is a token defect at its start (grammar `wertListenSpezifier2`;
  -- k22-static-classes-2026-10-24, `s17-in-bool2`, `s17-in-boolf`).
  if index ≥ 1 && valueListOperators.contains id && !(← inFollowsInCall) then
    match ← peek with
    | some (.string _) | some (.number _) | some (.symbol "-") | some (.symbol "[") => pure ()
    | _ => failHere .incompleteInput
  let expr ← condition false
  let rangeEnd ← if ← acceptKeyword "To" then pure (some (← condition false)) else pure none
  return .mk expr rangeEnd
end

private def preamble : P (List String) := do
  if ← acceptKeyword "@SuppressWarning" then
    expectSymbol "("
    let name ← match ← peek with
      | some (.name name _) => advance; pure name
      | _ => failHere .expectedTokenNotFound
    expectSymbol ")"
    return [name]
  else return []

/-- Read one condition or operation text from its lexemes, with the events completed before the text
ended or failed, in completion order. -/
def parseLexemesRecording (lexemes : Array Lexeme) : Except SyntaxError Text × Array ParseEvent :=
  let grammar : P Text := do
    let suppressed ← preamble
    let body ← condition true
    if (← peek).isSome then failHere .unexpectedToken
    return { suppressed, body }
  run grammar lexemes

/-- Read one condition or operation text from its lexemes. -/
def parseLexemes (lexemes : Array Lexeme) : Except SyntaxError Text :=
  (parseLexemesRecording lexemes).1

/-- Read one condition or operation text in a model's language. -/
def parseText (language : Language) (text : String) : Except SyntaxError Text := do
  parseLexemes (← lex language text)

/-- Model reference attributes name declarations, including DSL keywords. The retained temporal
filter matrix targets fields named Date and Time without expression-language quoting. -/
def parseModelPath (language : Language) (text : String) : Except SyntaxError Path := do
  let lexemes ← lex language text (recognizeKeywords := false)
  let grammar : P Path := do
    let result ← path
    if (← peek).isSome then failHere .unexpectedToken
    return result
  (run grammar lexemes).1

mutual
/-- Whether every parenthesis groups a condition in a condition position (spec §12.3): a whole
condition, a connective's part, a parenthesised condition's body or a filter body. A parenthesised
comparison side, operation, argument or whole computation operation is `MVK_UNEXPECTED_TOKEN`. The
grammar reads them all as one node, so this law is checked on the tree once the text's position,
condition or operation, is known. -/
partial def Expr.parensLegal (inCondition : Bool) : Expr → Bool
  | .parens body => inCondition && body.parensLegal true
  | .logic _ parts => parts.all (·.parensLegal true)
  | .compare _ left right => left.parensLegal false && right.parensLegal false
  | .arith _ left right => left.parensLegal false && right.parensLegal false
  | .braces body => body.parensLegal false
  | .value reference | .entity reference => reference.parensLegal
  | .call _ arguments listed scope =>
      (arguments ++ listed.getD []).all (fun
        | .mk expr rangeEnd =>
            expr.parensLegal false && rangeEnd.all (·.parensLegal false)) &&
        scope.all (·.parensLegal)
  | _ => true

partial def Reference.parensLegal (reference : Reference) : Bool :=
  (match reference.index with
    | some (.reference key) => key.parensLegal
    | _ => true) && reference.filter.all (·.parensLegal true)
end

end A12Kernel.Dm
