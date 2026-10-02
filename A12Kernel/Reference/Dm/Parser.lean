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

private abbrev P := StateT Nat (ReaderT (Array Lexeme) (Except SyntaxError))

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
  | some (.name name) => advance; return { name, star := ← acceptSymbol "*" }
  | _ => failHere .expectedTokenNotFound

private partial def segments : P (List Segment) := do
  let first ← segment
  if ← acceptSymbol "/" then return first :: (← segments) else return [first]

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
  | some (.name label) => advance; return (1, some label)
  | _ => return (1, none)

private def path : P Path := do
  let correlated ← acceptSymbol "$"
  let absolute ← acceptSymbol "/"
  let (ups, turningPoint) ← if absolute then pure (0, none) else ups
  let segments ← if ups == 0 then segments
    else if ← acceptSymbol "/" then segments else pure []
  return { correlated, absolute, ups, turningPoint, segments }

private def reference : P Reference := do
  let target ← path
  let index ← if ← acceptKeyword "For" then
      match ← peek with
      | some (.string text) => advance; pure (some (IndexKey.literal text))
      | _ => pure (some (.path (← path)))
    else pure none
  let category ← if ← acceptSymbol "->" then
      match ← peek with
      | some (.name name) => advance; pure (some name)
      | _ => failHere .expectedTokenNotFound
    else pure none
  return { path := target, index, category }

mutual
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
      | some (.name name) => advance; return .custom name
      | _ => failHere .expectedTokenNotFound
  | some (.keyword id) =>
      if separatorKeywords.contains id then failHere .incompleteInput
      advance
      if ← acceptSymbol "(" then call id else return .constant id
  | some (.name _) | some (.symbol "/") | some (.symbol "..") | some (.symbol "$") =>
      return .entity (← reference)
  | _ => failHere .incompleteInput

private partial def call (id : String) : P Expr := do
  if ← acceptSymbol ")" then return .call id [] none none
  let arguments ← argumentList
  let listed ← if ← acceptKeyword "In" then pure (some (← argumentList)) else pure none
  let scope ← if ← acceptKeyword "@From" then pure (some (← path)) else pure none
  expectSymbol ")"
  return .call id arguments listed scope

private partial def argumentList : P (List Argument) := do
  let first ← argument
  if ← acceptSymbol "," then return first :: (← argumentList) else return [first]

private partial def argument : P Argument := do
  let expr ← condition false
  let rangeEnd ← if ← acceptKeyword "To" then pure (some (← condition false)) else pure none
  let filter ← if ← acceptKeyword "Having" then pure (some (← condition false)) else pure none
  return .mk expr rangeEnd filter
end

private def preamble : P (List String) := do
  if ← acceptKeyword "@SuppressWarning" then
    expectSymbol "("
    let name ← match ← peek with
      | some (.name name) => advance; pure name
      | _ => failHere .expectedTokenNotFound
    expectSymbol ")"
    return [name]
  else return []

/-- Read one condition or operation text in a model's language. -/
def parseText (language : Language) (text : String) : Except SyntaxError Text := do
  let lexemes ← lex language text
  let grammar : P Text := do
    let suppressed ← preamble
    let body ← condition true
    if (← peek).isSome then failHere .unexpectedToken
    return { suppressed, body }
  (grammar.run' 0).run lexemes

end A12Kernel.Dm
