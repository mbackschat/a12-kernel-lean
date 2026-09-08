/-! # The form-level condition constructs, and the two classes an A12 model draws from them

The condition language carries a family of **form-level** constructs — six keywords naming a root
group and asking whether that form is present, absent, or numbered consecutively. They belong to the
H-model dialect, and an A12 document model refuses every one of them. Which class it refuses with
depends on something a consumer would not guess: the model's declared **condition language**.

**The keywords are German-only literals.** They have no English spelling in the shared lexer, so on a
model whose condition language is en_US they do not lex at all and the construct draws the generic
unexpected-token class — the same class a misspelling draws. On a de_DE model they lex, reach the
checker, and draw the construct's own class. So the identical authored text produces two different
diagnostics on two models differing only in that one setting, and only one of them says what is
actually wrong ([checkpoint](../../docs/SOURCES.md#src-form-condition-constructs)).

**The construct's own class shadows the two that follow it.** The checker that names the construct
runs before the one that inspects its argument, so an A12 model never reaches the wildcard checks:
neither the star-forbidden class nor the star-required one can fire. That is measured rather than
read — all six keywords were probed **with and without** the star, and every one drew the construct
class, which is exactly the pair of rows a shadowing claim needs.

**A sibling family does not lex even in German.** The row-level constructs — three keywords asking
whether a repeatable group's rows are contiguous, ascending, or unique — draw the unexpected-token
class on a German A12 model too, so they are absent from the active grammar rather than refused by a
checker. Their checker's own class is therefore unreachable from the condition surface.

**What this module does not model** is the H-model branch. For a model that is *not* an A12 document
model the construct is admitted and the wildcard checks do run, and no route this project has can
reach that branch; inventing it here would state an unmeasured claim, so the two classes behind it are
listed with their keys and marked unreachable-from-A12 instead.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A model's declared condition language. It selects the active keyword set, and this family is the
sharpest case: the constructs exist in only one of the two. -/
inductive ConditionLanguage where
  | english
  | german
  deriving Repr, DecidableEq

/-- The six form-level construct keywords. Named for what they ask rather than transliterated, since
the surface spelling is the German literal and belongs in the checkpoint, not in an identifier. -/
inductive FormConditionKeyword where
  | rootGroupSpecified
  | rootGroupNotSpecified
  | atLeastOneRootGroupSpecified
  | noRootGroupSpecified
  | rootGroupNotConsecutive
  | subScopeNotConsecutive
  deriving Repr, DecidableEq

namespace FormConditionKeyword

/-- Every keyword of the family. -/
def all : List FormConditionKeyword :=
  [.rootGroupSpecified, .rootGroupNotSpecified, .atLeastOneRootGroupSpecified,
   .noRootGroupSpecified, .rootGroupNotConsecutive, .subScopeNotConsecutive]

/-- Whether the construct is one of the two the H-model branch would require a star for. Carried so
the shadowing law can say the distinction exists upstream and makes no difference here. -/
def requiresWildcardInHModel : FormConditionKeyword → Bool
  | .atLeastOneRootGroupSpecified | .noRootGroupSpecified => true
  | _ => false

end FormConditionKeyword

/-- The three row-level construct keywords, which do not lex in either language. -/
inductive RowConditionKeyword where
  | rowsContiguous
  | rowsNotAscending
  | rowNotUnique
  deriving Repr, DecidableEq

namespace RowConditionKeyword

def all : List RowConditionKeyword := [.rowsContiguous, .rowsNotAscending, .rowNotUnique]

end RowConditionKeyword

/-- A class either family can draw. -/
inductive RootGroupConditionRefusal where
  /-- The keyword is not in the active language's lexer, so the parser stops on the token. -/
  | unexpectedToken
  /-- The construct is named and the model is an A12 document model. -/
  | invalidRootGroupConstr
  /-- H-model branch: a star where the construct forbids one. -/
  | conditionWithWildcard
  /-- H-model branch: no star where the construct requires one. -/
  | conditionWithoutRepeatableRootGroup
  /-- The row-level construct's own argument class. -/
  | invalidParamsForOp
  deriving Repr, DecidableEq

namespace RootGroupConditionRefusal

/-- The exact catalog key. -/
def catalogKey : RootGroupConditionRefusal → String
  | .unexpectedToken => "MVK_UNEXPECTED_TOKEN"
  | .invalidRootGroupConstr => "MVK_INVALID_ROOT_GROUP_CONSTR"
  | .conditionWithWildcard => "MVK_CONDITION_WITH_WILDCARD"
  | .conditionWithoutRepeatableRootGroup => "MVK_CONDITION_WITHOUT_REPEATABLE_ROOTGROUP"
  | .invalidParamsForOp => "MVK_INVALID_PARAMS_FOR_OP"

def all : List RootGroupConditionRefusal :=
  [.unexpectedToken, .invalidRootGroupConstr, .conditionWithWildcard,
   .conditionWithoutRepeatableRootGroup, .invalidParamsForOp]

/-- The classes an A12 document model can actually draw from these two families. The complement is
what the H-model branch owns. -/
def reachableFromA12 : List RootGroupConditionRefusal :=
  [.unexpectedToken, .invalidRootGroupConstr]

end RootGroupConditionRefusal

/-- **The A12 refusal for a form-level construct.** The star is an argument precisely so the law below
can state that it makes no difference: the construct's own class is decided before anything reads the
argument. -/
def a12FormConditionRefusal (language : ConditionLanguage) (_keyword : FormConditionKeyword)
    (_starred : Bool) : RootGroupConditionRefusal :=
  match language with
  | .english => .unexpectedToken
  | .german => .invalidRootGroupConstr

/-- **The A12 refusal for a row-level construct.** Absent from the active grammar in both languages,
so the language makes no difference here — the mirror image of the form family, and the reason the two
are modelled together. -/
def a12RowConditionRefusal (_language : ConditionLanguage) (_keyword : RowConditionKeyword) :
    RootGroupConditionRefusal :=
  .unexpectedToken

end A12Kernel
