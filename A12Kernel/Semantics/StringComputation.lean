import A12Kernel.Semantics.Observation
import A12Kernel.Document

/-! # A12Kernel.Semantics.StringComputation — one-target-instance String computation

This capsule implements the first non-repeatable, unconditional subset of `spec/09-computations.md` (§11): resolved String-field reads, String literals, concatenation, root storage, and kernel-style delta projection. Expression evaluation, root storage, and delta reporting are deliberately separate because an empty field contributes `""` inside concatenation, yet a final empty String is not stored and only clears a previously filled target.
-/

namespace A12Kernel

/-- A String that may legally exist in a computed target. The constructor rules out the empty stored value which the kernel's root String store treats as no calculation. -/
structure StoredString where
  text : String
  nonempty : text ≠ ""
  deriving Repr, DecidableEq

/-- Result of evaluating a String expression before the root store consumes it. `noValue` is a clean absent field read, `text ""` is an evaluated empty text such as an all-empty concatenation, and `poison` preserves formal invalidity for downstream computations. -/
inductive StringTerm where
  | noValue
  | text (value : String)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

namespace StringTerm

/-- Concatenation is the consuming context that maps a clean absent operand to the empty contribution. A left poison wins because computation reads are ordered. -/
def concat : StringTerm → StringTerm → StringTerm
  | .poison cause, _ => .poison cause
  | _, .poison cause => .poison cause
  | .noValue, .noValue => .text ""
  | .noValue, .text right => .text right
  | .text left, .noValue => .text left
  | .text left, .text right => .text (left ++ right)

end StringTerm

/-- A malformed low-level context is outside the computation language. Ordinary formal invalidity is not a fault: it is represented by `StringTerm.poison`. -/
inductive StringComputationFault where
  | fieldKindMismatch (field : FieldId)
  deriving Repr, DecidableEq

/-- Pure, already-resolved read context for one non-repeatable computation instance. Model/path checking remains a later elaboration boundary. -/
structure StringComputationContext where
  read : FieldId → CheckedCell

namespace StringComputationContext

/-- Refine one already-resolved checked field into the String-expression term domain. Empty and formal invalidity remain distinct; a low-level non-String value is a context fault. -/
def readTerm (context : StringComputationContext) (field : FieldId) :
    Except StringComputationFault StringTerm :=
  match observeCell .computation (context.read field) with
  | .empty => pure .noValue
  | .value (.str text) => if text.isEmpty then pure .noValue else pure (.text text)
  | .value _ => throw (.fieldKindMismatch field)
  | .poison cause => pure (.poison cause)
  | .unknown cause => pure (.poison cause)

end StringComputationContext

/-- Parser-independent String expression admitted by the first computation capsule. -/
inductive StringExpr where
  | field (field : FieldId)
  | literal (value : String)
  | concat (left right : StringExpr)
  deriving Repr, DecidableEq

namespace StringExpr

/-- Evaluate without deciding whether the resulting text can be stored. The right operand is not consulted after a left poison. -/
def eval (context : StringComputationContext) : StringExpr → Except StringComputationFault StringTerm
  | StringExpr.field fieldId => context.readTerm fieldId
  | StringExpr.literal value => pure (.text value)
  | StringExpr.concat left right => do
      let leftResult ← left.eval context
      match leftResult with
      | .poison cause => pure (.poison cause)
      | _ => pure (StringTerm.concat leftResult (← right.eval context))

end StringExpr

/-- Decision at the root String target boundary. A clean no-value and poison are intentionally distinct even though both can project to the same immediate `CLEARED` delta. -/
inductive StringStore where
  | noValue
  | produced (value : StoredString)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

namespace StringTerm

/-- Consume an expression result at the root target. Final empty text is no stored value, irrespective of whether it came from a literal or concatenation. -/
def store : StringTerm → StringStore
  | StringTerm.noValue => .noValue
  | StringTerm.poison cause => .poison cause
  | StringTerm.text textValue =>
      if nonempty : textValue ≠ "" then
        .produced { text := textValue, nonempty }
      else
        .noValue

end StringTerm

namespace StringExpr

/-- Evaluate and apply the root String storage rule, without mutating a document. -/
def evaluate (expression : StringExpr) (context : StringComputationContext) :
    Except StringComputationFault StringStore := do
  pure (← expression.eval context).store

end StringExpr

/-- Prior state used by the library delta projector. The target cannot contain an empty stored String by construction. -/
inductive PriorStringTarget where
  | empty
  | filled (value : StoredString)
  deriving Repr, DecidableEq

/-- Observable computation delta for this clean, unconstrained String capsule. Target-check failures and their attempted values require a later, evidence-backed store outcome rather than an unreachable constructor here. -/
inductive StringDelta where
  | value (stored : StoredString)
  | cleared
  deriving Repr, DecidableEq

namespace StringStore

/-- Project a semantic store decision against the previous target. Produced values are reported only when typed-changed; quiet no-value and poison clear only a previously filled target. -/
def projectDelta (result : StringStore) : PriorStringTarget → Option StringDelta
  | .empty => match result with
      | .produced value => some (.value value)
      | .noValue | .poison _ => none
  | .filled previous => match result with
      | .produced value => if value == previous then none else some (.value value)
      | .noValue | .poison _ => some .cleared

end StringStore

end A12Kernel
