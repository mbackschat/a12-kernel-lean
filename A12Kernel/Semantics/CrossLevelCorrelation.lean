import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Semantics.CrossLevelCorrelation — one star, two captured levels

This capsule keeps the correlated-filter core shared while adding one exact topology:
the rule's captured environment contains a starred level and one nested descendant,
whereas each filter candidate binds only the starred level. It excludes multiple
stars, joins, general nested paths, or repeatable computation. The caller supplies the
parent/descendant relation; checked model-derived topology remains outside this capsule.
-/

namespace A12Kernel

/-- One starred candidate level observed from a two-level rule environment. -/
structure TwoLevelOuterStarContext where
  starLevel : RepeatableLevel
  descendantLevel : RepeatableLevel
  candidates : List RowIndex
  read : Env → FieldId → CheckedCell

/-- Reopening the one starred level gives a candidate environment with that coordinate
    only. The nested rule coordinate is intentionally not copied into the candidate. -/
def TwoLevelOuterStarContext.candidateEnv
    (context : TwoLevelOuterStarContext) (row : RowIndex) : Env :=
  [(context.starLevel, row)]

def TwoLevelOuterStarContext.asCorrelationContext
    (context : TwoLevelOuterStarContext) : CorrelationContext :=
  { read := context.read }

/-- One rule instance captures both its row at the starred level and its row at the
    nested descendant level. -/
structure CapturedTwoLevelOuterStarContext where
  rows : TwoLevelOuterStarContext
  outerStarRow : RowIndex
  outerDescendantRow : RowIndex

def CapturedTwoLevelOuterStarContext.outerEnv
    (context : CapturedTwoLevelOuterStarContext) : Env :=
  [(context.rows.starLevel, context.outerStarRow),
    (context.rows.descendantLevel, context.outerDescendantRow)]

def CapturedTwoLevelOuterStarContext.frame
    (context : CapturedTwoLevelOuterStarContext)
    (innerRow : RowIndex) : CorrelationFrame :=
  { innerEnv := context.rows.candidateEnv innerRow
    outerEnv := context.outerEnv }

def SingleCorrelatedStar.keepsCrossLevel (star : SingleCorrelatedStar)
    (context : CapturedTwoLevelOuterStarContext) (innerRow : RowIndex) : Bool :=
  star.having.condition.keepsEnvironment context.rows.asCorrelationContext
    context.outerEnv (context.rows.candidateEnv innerRow)

/-- Straightforward reference meaning: scan the one starred level in document order and
    keep only candidates whose filter is known true. -/
def SingleCorrelatedStar.selectCrossLevel (star : SingleCorrelatedStar)
    (context : CapturedTwoLevelOuterStarContext) : List RowIndex :=
  context.rows.candidates.filter (star.keepsCrossLevel context)

end A12Kernel
