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
whose path closed, and the steps of a path still open, each step a segment the parse read up to its `/`. -/
inductive ParseEvent where
  | reference (path : Path)
  | openPath (path : Path)
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

/-- Keywords that never open an operand. -/
private def separatorKeywords : List String :=
  ["And", "Or", "In", "To", "Having", "For", "@From", "@SuppressWarning", "PatternMatched",
   "PatternViolated", "DiffersWithToleranceRange1", "DiffersWithToleranceRange2",
   "DiffersWithToleranceRange5", "DiffersWithToleranceRange10"]

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

/-- The segments after `header`'s prefix, each step read up to its `/` recorded as the open path so far. -/
private partial def segments (header : Path) : P (List Segment) := do
  let first ← segment
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

mutual
private partial def indexSuffix : P (Option IndexKey) := do
  if ← acceptKeyword "For" then
    match ← peek with
    | some (.string text) => advance; pure (some (.literal text))
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
  let index ← indexSuffix
  let filter ← if ← acceptKeyword "Having" then pure (some (← condition false)) else pure none
  return { path := target, index, category, filter }

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
      advance
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
      return .entity (← reference)
  | _ => failHere .incompleteInput

private partial def call (id : String) : P Expr := do
  if ← acceptSymbol ")" then return .call id [] none none
  let arguments ← argumentList
  -- datumParam uses entitySpec; digit-only names are identifiers here (KF532; grammar idName).
  -- Keep invalid shapes for the ordered admission walk, where earlier entity failures still win.
  let arguments := if id == "Date" || id == "Time" then arguments.map (fun
      | .mk (.number digits) none =>
          if !digits.isEmpty && digits.toList.all Char.isDigit then
            .mk (.entity { path := { segments := [{ name := digits, star := false }] } }) none
          else .mk (.number digits) none
      | argument => argument) else arguments
  let listed ← if ← acceptKeyword "In" then pure (some (← argumentList)) else pure none
  let scope ← if ← acceptKeyword "@From" then pure (some (← reference)) else pure none
  expectSymbol ")"
  return .call id arguments listed scope

private partial def argumentList : P (List Argument) := do
  let first ← argument
  if ← acceptSymbol "," then return first :: (← argumentList) else return [first]

private partial def argument : P Argument := do
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
