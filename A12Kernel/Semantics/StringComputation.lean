import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.String
import A12Kernel.Document

/-! # A12Kernel.Semantics.StringComputation — one-target-instance String computation

This capsule implements the first non-repeatable, unconditional subset of `spec/09-computations.md` (§11): resolved String-field reads, String literals, concatenation, root storage, positive target-length checks, payloadful `ERRORED`, value-only application, and kernel-style delta projection. Expression evaluation, root storage, target checking, application, and delta reporting remain separate because each exposes a different semantic boundary.
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
def evaluate (expression : StringExpr) (context : StringComputationContext) :
    Except StringComputationFault StringStore := do
  pure (← expression.eval context).store

end StringExpr

/-- A positive declared String-length bound. The current checked projection deliberately rejects nonpositive declarations until their separate runtime treatment is differentially closed. -/
structure PositiveStringLength where
  value : Nat
  positive : 0 < value
  deriving Repr, DecidableEq

/-- The closed target-length fragment. A model declaring both bounds remains outside this first separating capsule. -/
inductive StringTargetLengthPolicy where
  | unconstrained
  | minimum (bound : PositiveStringLength)
  | maximum (bound : PositiveStringLength)
  deriving Repr, DecidableEq

/-- Language-neutral first-failure cause for the admitted String target-length checks. -/
inductive StringTargetError where
  | tooShort
  | tooLong
  deriving Repr, DecidableEq

/-- A value that needs an earlier reduced-target clause which this length-only capsule does not yet model. This is fail-closed fragment routing, not a kernel computation outcome. -/
inductive StringTargetCheckFault where
  | unsupportedLineBreak
  deriving Repr, DecidableEq

/-- Result after the root write attempt has passed through the admitted target-length policy. Target rejection is an ordinary payloadful result, not a computation fault or poison. -/
inductive StringTargetOutcome where
  | noValue
  | accepted (value : StoredString)
  | errored (attempted : StoredString) (cause : StringTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Result of routing a root write through the admitted target-check fragment. `unsupported` is a fail-closed model boundary, not an external computation result. -/
inductive StringTargetCheckResult where
  | supported (outcome : StringTargetOutcome)
  | unsupported (fault : StringTargetCheckFault)
  deriving Repr, DecidableEq

namespace StringTargetLengthPolicy

/-- Classify the sole admitted target-length violation after the preceding line-break clause has been excluded. Combined policies and their order remain outside this capsule. -/
def admittedViolation (policy : StringTargetLengthPolicy) (attempted : StoredString)
    (_noLineBreak : containsLineBreak attempted.text = false) : Option StringTargetError :=
  match policy with
  | .unconstrained => none
  | .minimum bound =>
      let length := utf16CodeUnitLength attempted.text
      if length < bound.value then some .tooShort else none
  | .maximum bound =>
      let length := utf16CodeUnitLength attempted.text
      if bound.value < length then some .tooLong else none

/-- Apply only the admitted target-length validation to a root write attempt. No-value and poison bypass target validation and remain distinguishable; a produced value outside the length-only fragment fails closed. -/
def check (policy : StringTargetLengthPolicy) : StringStore → StringTargetCheckResult
  | .noValue => .supported .noValue
  | .poison cause => .supported (.poison cause)
  | .produced attempted =>
      if noLineBreak : containsLineBreak attempted.text = false then
        match policy.admittedViolation attempted noLineBreak with
        | none => .supported (.accepted attempted)
        | some cause => .supported (.errored attempted cause)
      else
        .unsupported .unsupportedLineBreak

end StringTargetLengthPolicy

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

namespace StringTargetCheckResult

/-- Apply a projection only to a supported target outcome. The outer `none` preserves fragment rejection separately from any `none` returned by the projection itself. -/
def mapOutcome (f : StringTargetOutcome → α) : StringTargetCheckResult → Option α
  | .supported outcome => some (f outcome)
  | .unsupported _ => none

end StringTargetCheckResult

namespace StringStore

/-- Preserve the original pre-target-check delta API without manufacturing a post-check accepted outcome. -/
def projectDelta (result : StringStore) (prior : PriorStringTarget) : Option StringDelta :=
  match result with
  | .produced value => StringDelta.projectValue value prior
  | .noValue | .poison _ => StringDelta.projectNoValue prior

end StringStore

end A12Kernel
