import A12Kernel.Reference.Dm.Negate
import A12Kernel.Reference.Dm.Parser

/-! # The `Non<Operation>` extension

An extension of the condition language, not part of the Kernel's: every predicate `Op` gains a
negated twin `NonOp`, written `Non` followed by `Op`'s spelling in the model's language
(`NonFieldFilled`, `NonFeldAngegeben`). `NonOp(args)` means the negation of `Op(args)`, and it is
lowered to Kernel text by the same complement table rule negation uses, so a lowered rule runs on the
Kernel and fires exactly where the original predicate is decided false.

A twin exists only where the complement does. `NonFieldValuesNotUnique` and the other predicates
without a complement in the language are refused, rather than given a silent region the Kernel
never measured. Comparisons have no twin, since each already has its complement operator.

The extension is read by its own entry, `parseNonText`: in the Kernel language `NonFieldFilled` stays
an ordinary name.
-/

namespace A12Kernel.Dm

/-- The keyword id a `Non` spelling names, by the rest of its spelling in the model's language. -/
def nonKeywordId? (language : Language) (spelling : String) : Option String := do
  guard (spelling.startsWith "Non")
  let base ← keywordId? language (spelling.drop 3).toString
  pure ("Non" ++ base)

/-- Re-read a name directly before `(` as a `Non` keyword when its rest spells one. -/
def markNonKeywords (language : Language) (lexemes : Array Lexeme) : Array Lexeme :=
  lexemes.mapIdx fun index lexeme =>
    match lexeme.token, lexemes[index + 1]?.map (·.token) with
    | .name spelling, some (.symbol "(") => match nonKeywordId? language spelling with
        | some id => { lexeme with token := .keyword id }
        | none => lexeme
    | _, _ => lexeme

/-- Read a condition text of the extension. -/
def parseNonText (language : Language) (text : String) : Except SyntaxError Text := do
  parseLexemes (markNonKeywords language (← lex language text))

mutual
/-- Replace every `NonOp(args)` by the negation of `Op(args)`. -/
def lowerNon : Expr → Except NegationRefusal Expr
  | .call id arguments listed scope => do
      let arguments ← lowerNonArguments arguments
      let listed ← match listed with
        | some items => some <$> lowerNonArguments items
        | none => pure none
      if id.startsWith "Non" then negate (.call (id.drop 3).toString arguments listed scope)
      else pure (.call id arguments listed scope)
  | .parens body => do pure (.parens (← lowerNon body))
  | .braces body => do pure (.braces (← lowerNon body))
  | .logic op parts => do pure (.logic op (← lowerNonParts parts))
  | .compare op left right => do pure (.compare op (← lowerNon left) (← lowerNon right))
  | .arith op left right => do pure (.arith op (← lowerNon left) (← lowerNon right))
  | other => pure other

def lowerNonParts : List Expr → Except NegationRefusal (List Expr)
  | [] => pure []
  | part :: rest => do
      -- A twin lowered to a connective list keeps its own bracket inside the enclosing list.
      let lowered := match ← lowerNon part with
        | expr@(.logic _ _) => .parens expr
        | expr => expr
      pure (lowered :: (← lowerNonParts rest))

def lowerNonArguments : List Argument → Except NegationRefusal (List Argument)
  | [] => pure []
  | .mk expr rangeEnd filter :: rest => do
      let rangeEnd ← match rangeEnd with
        | some finish => some <$> lowerNon finish
        | none => pure none
      let filter ← match filter with
        | some body => some <$> lowerNon body
        | none => pure none
      pure (.mk (← lowerNon expr) rangeEnd filter :: (← lowerNonArguments rest))
end

end A12Kernel.Dm
