import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.String
import A12Kernel.Semantics.StringFieldPolicy
import A12Kernel.Document

/-! # A12Kernel.Semantics.StringComputation — one-target-instance String computation

This capsule implements the first non-repeatable, unconditional subset of `spec/09-computations.md` (§11): resolved String-field reads, String literals, concatenation, root storage, declaration-owned ordinary target checks, payloadful `ERRORED`, value-only application, and kernel-style delta projection. Expression evaluation, root storage, target checking, application, and delta reporting remain separate because each exposes a different semantic boundary.
-/

namespace A12Kernel

/-- A nonempty rendered stored form. Target-specific legality is decided later, so this type also carries an attempted value retained by `ERRORED`. -/
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

/-- The String fragment uses the common checked scalar-computation read boundary without adding a second context representation. -/
abbrev StringComputationContext := ScalarComputationContext

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

/-- Parser-independent String expression admitted by the first computation capsule. Parameterizing only the leaf lets checked lowering reuse the runtime tree without defining a parallel expression language. -/
inductive StringExpr (Atom : Type := FieldId) where
  | field (field : Atom)
  | literal (value : String)
  | concat (left right : StringExpr Atom)
  deriving Repr, DecidableEq

namespace StringExpr

/-- Evaluate without deciding whether the resulting text can be stored. The right operand is not consulted after a left poison. -/
def eval (context : StringComputationContext) : StringExpr FieldId → Except StringComputationFault StringTerm
  | StringExpr.field fieldId => context.readTerm fieldId
  | StringExpr.literal value => pure (.text value)
  | StringExpr.concat left right => do
      let leftResult ← left.eval context
      match leftResult with
      | .poison cause => pure (.poison cause)
      | _ => pure (StringTerm.concat leftResult (← right.eval context))

end StringExpr

/-- Root write attempt before target-specific validation. A clean no-value and poison are intentionally distinct even though both can project to the same immediate `CLEARED` delta. -/
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
def evaluate (expression : StringExpr FieldId) (context : StringComputationContext) :
    Except StringComputationFault StringStore := do
  pure (← expression.eval context).store

end StringExpr

/-- Language-neutral first-failure cause for ordinary computed-String target checking. It is shared with the declaration-owned scalar policy because both use the same basic format clauses. -/
abbrev StringTargetError := StringFieldError

/-- Result after the root write attempt has passed through the ordinary target policy. Target rejection is an ordinary payloadful result, not a computation fault or poison. -/
inductive StringTargetOutcome where
  | noValue
  | accepted (value : StoredString)
  | errored (attempted : StoredString) (cause : StringTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Apply the declaration-owned basic String clauses to a root write attempt. Checking may normalize CRLF for length measurement, but an accepted or rejected result retains the exact attempted payload. No-value and poison bypass target validation unchanged. -/
def StringFieldPolicy.checkTarget (policy : StringFieldPolicy) : StringStore → StringTargetOutcome
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .produced attempted =>
      match policy.checkText attempted.text with
      | .ok _ => .accepted attempted
      | .error cause => .errored attempted cause

/-- Prior state used by the library delta projector. The target cannot contain an empty stored String by construction. -/
inductive PriorStringTarget where
  | empty
  | filled (value : StoredString)
  deriving Repr, DecidableEq

/-- Observable computation delta. `errored` always retains the attempted nonempty stored form and the target-check cause. -/
inductive StringDelta where
  | value (stored : StoredString)
  | cleared
  | errored (attempted : StoredString) (cause : StringTargetError)
  deriving Repr, DecidableEq

namespace StringDelta

/-- Project an already selected nonempty value against the previous target without assigning a target-check phase to that value. -/
def projectValue (value : StoredString) : PriorStringTarget → Option StringDelta
  | .empty => some (.value value)
  | .filled previous => if value == previous then none else some (.value value)

/-- Project the absence of a stored value against the previous target. -/
def projectNoValue : PriorStringTarget → Option StringDelta
  | .empty => none
  | .filled _ => some .cleared

end StringDelta

namespace StringTargetOutcome

/-- Project a checked target outcome against the previous target. Accepted values are change-sensitive; target errors are unconditional; quiet no-value and poison clear only a previously filled target. -/
def projectDelta (result : StringTargetOutcome) (prior : PriorStringTarget) :
    Option StringDelta :=
  match result with
  | .errored attempted cause => some (.errored attempted cause)
  | .accepted value => StringDelta.projectValue value prior
  | .noValue | .poison _ => StringDelta.projectNoValue prior

/-- Value-only view after applying a computation result. It deliberately does not claim whether the resulting empty target instance is absent or present-empty. -/
def appliedValue : StringTargetOutcome → Option StoredString
  | .accepted value => some value
  | .noValue | .errored _ _ | .poison _ => none

end StringTargetOutcome

namespace StringStore

/-- Preserve the original pre-target-check delta API without manufacturing a post-check accepted outcome. -/
def projectDelta (result : StringStore) (prior : PriorStringTarget) : Option StringDelta :=
  match result with
  | .produced value => StringDelta.projectValue value prior
  | .noValue | .poison _ => StringDelta.projectNoValue prior

end StringStore

end A12Kernel
