import A12Kernel.Reference.Dm.Print
import A12Kernel.Reference.Dm.LowerCore

/-! # Negating a rule condition

A rule fires where its condition holds, so the rule that fires where it is definitely false is the
original with a negated condition. The language has no `Not` (spec §A.2), so negation pushes through
`And` and `Or` by De Morgan and replaces each predicate with its complement, using only operators
the Kernel already has. The output is a parse tree in the grammar's own shape, printable with
`printText` and runnable on the Kernel.

A complement is the predicate that fires exactly where the original is decided false. Most pairs are
one predicate each (`FieldFilled` and `FieldNotFilled`, `>` and `<=`); three have only a compound or a
count comparison as complement, and a predicate with no complement in the language refuses the
negation. Each pair was run on the Kernel over documents separating filled, empty, formally invalid,
uninstantiated and over-limit cells, and no pair fired both members
([grid](../../../evidence/kernel-30.8.1/captures/negation-pair-grid-2026-10-02/request.json)).

Whether the negated rule is legal is the static check's question: an iteration guard the negation
turns into its complement, or an error field the output no longer reads, refuses it there. The
firing polarity of the output and the empty-instance gate are not preserved by negation.
-/

namespace A12Kernel.Dm

/-- A condition no complement exists for, named by its construct. -/
structure NegationRefusal where
  construct : String
  deriving Repr, BEq

/-- The predicate pairs with a single-predicate complement, each listed once. -/
def complementPairs : List (String × String) := [
  ("FieldFilled", "FieldNotFilled"), ("GroupFilled", "GroupNotFilled"),
  ("AllFieldsFilled", "NotAllFieldsFilled"), ("AtLeastOneFieldFilled", "NoFieldFilled"),
  ("AllGroupsFilled", "NotAllGroupsFilled"), ("AtLeastOneGroupFilled", "NoGroupFilled"),
  ("FieldValueIncludedInValueList", "FieldValueNotIncludedInValueList"),
  ("AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList"),
  ("Valid", "Invalid")]

def complementId? (id : String) : Option String :=
  (complementPairs.find? (·.1 == id)).map (·.2) <|> (complementPairs.find? (·.2 == id)).map (·.1)

def CompareOp.complement? : CompareOp → Option CompareOp
  | .eq => some .ne | .ne => some .eq
  | .lt => some .ge | .ge => some .lt
  | .le => some .gt | .gt => some .le
  | .patternMatched => some .patternViolated | .patternViolated => some .patternMatched
  | .tolerance _ => none

/-- A part of a connective list, in parentheses when it is itself a connective list. -/
private def asPart : Expr → Expr
  | expr@(.logic _ _) => .parens expr
  | expr => expr

mutual
/-- The negated condition, or the first predicate without a complement. -/
def negate : Expr → Except NegationRefusal Expr
  | .parens body => do pure (.parens (← negate body))
  | .logic op parts => do
      let dual := match op with | .and => LogicOp.or | .or => .and
      pure (.logic dual (← negateParts parts))
  | .compare op left right => match op.complement? with
      | some complement => pure (.compare complement left right)
      | none => throw { construct := "Comparison/" ++ (CompareOp.spelling .english op) }
  -- A complement shares its original's argument shape, so an `In` list and an `@From` scope stay.
  | .call id arguments listed scope => match complementId? id, id, listed, scope with
      | some complement, _, _, _ => pure (.call complement arguments listed scope)
      | none, "FieldsNotCollectivelyFilled", none, none => pure (.parens (.logic .or
          [.call "AllFieldsFilled" arguments none none, .call "NoFieldFilled" arguments none none]))
      | none, "GroupsNotCollectivelyFilled", none, none => pure (.parens (.logic .or
          [.call "AllGroupsFilled" arguments none none, .call "NoGroupFilled" arguments none none]))
      | none, "MoreThanOneFieldFilled", none, none =>
          pure (.compare .le (.call "NumberOfFilledFields" arguments none none) (.number "1"))
      | none, "NotExactlyOneFieldFilled", none, none =>
          pure (.compare .eq (.call "NumberOfFilledFields" arguments none none) (.number "1"))
      | none, _, _, _ => throw { construct := id }
  | .custom _ => throw { construct := "CustomCondition" }
  | other => throw { construct := other.construct }

def negateParts : List Expr → Except NegationRefusal (List Expr)
  | [] => pure []
  | part :: rest => do pure (asPart (← negate part) :: (← negateParts rest))
end

/-- Negate a whole condition text, keeping its suppressed warnings. -/
def negateText (text : Text) : Except NegationRefusal Text := do
  pure { text with body := ← negate text.body }

end A12Kernel.Dm
