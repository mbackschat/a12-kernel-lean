import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.String
import A12Kernel.Semantics.Enumeration
import A12Kernel.Semantics.StringFieldPolicy
import A12Kernel.Document

/-! # A12Kernel.Semantics.StringComputation — one-target-instance String computation

This capsule implements a non-repeatable String computation core from `spec/09-computations.md` (§11): resolved String-field reads, Number `FieldValueAsString` reads, String literals, concatenation, checked `RangeAsString`, root storage, declaration-owned ordinary target checks, payloadful `ERRORED`, value-only application, and kernel-style delta projection. Expression evaluation, root storage, target checking, application, and delta reporting remain separate because each exposes a different semantic boundary.
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
  | guardBinding (error : ComputationConditionError)
  | fieldKindMismatch (field : FieldId)
  | invalidRange (start finish : Nat)
  | unalignedUtf16Range (field : FieldId) (start finish : Nat)
  | targetPatternUnavailable (field : FieldId)
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

/-- Parser-independent String expression admitted by the first computation capsule. Parameterizing field identity and category selection lets checked lowering resolve authored names to positional mappings in the same tree. -/
inductive StringExpr (Atom : Type := FieldId) (Category : Type := ResolvedEnumerationCategory) where
  | field (field : Atom)
  | category (field : Atom) (projection : Category)
  | fieldValueAsString (field : Atom)
  | literal (value : String)
  | range (field : Atom) (start finish : Nat)
  | concat (left right : StringExpr Atom Category)
  deriving Repr, DecidableEq

/-- Storage forgets comparison provenance while preserving formal poison, for fixed and row targets. -/
def StringTerm.ofOperand : SimpleComparisonOperand String → StringTerm
  | .notEvaluated => .noValue
  | .value value _ => .text value
  | .unknown cause => .poison cause

namespace StringExpr

/-- A String read keeps omission provenance independently of its text. Validation and computation
share the operand domain; computation alone stops at a reached formal cause (String grid, 2026-10-04). -/
def readOperandAt (phase : Phase) (read : FieldId → CheckedCell) (fieldId : FieldId) :
    Except StringComputationFault (SimpleComparisonOperand String) :=
  match observeCell phase (read fieldId) with
  | .empty => pure .notEvaluated
  | .value (.str text) | .value (.enum text) =>
      if text.isEmpty then pure .notEvaluated else pure (.value text true)
  | .value _ => throw (.fieldKindMismatch fieldId)
  | .poison cause | .unknown cause => pure (.unknown cause)

/-- Absence contributes empty text without becoming fixed provenance; formal unavailability keeps
its cause. The range and concatenation runtime grid separates these from empty comparison results. -/
def concatOperands : SimpleComparisonOperand String → SimpleComparisonOperand String →
    SimpleComparisonOperand String
  | .unknown cause, _ | _, .unknown cause => .unknown cause
  | .notEvaluated, .notEvaluated => .value "" false
  | .notEvaluated, .value right _ => .value right false
  | .value left _, .notEvaluated => .value left false
  | .value left leftGiven, .value right rightGiven => .value (left ++ right) (leftGiven && rightGiven)

/-- One ordered String evaluator serves validation, guards and stores. The caller provides already
classified String or Number-text reads, so storage-regime selection remains with the document. -/
def evalOperandWith (phase : Phase)
    (read : FieldId → Except StringComputationFault (SimpleComparisonOperand String)) :
    StringExpr FieldId → Except StringComputationFault (SimpleComparisonOperand String)
  | .field fieldId | .fieldValueAsString fieldId => read fieldId
  | .category fieldId projection => do
      match ← read fieldId with
      | .value stored given =>
          match projection.categoryTokenFor? stored with
          | some text => pure (.value text given)
          | none => pure (.unknown .malformed)
      | other => pure other
  | .literal value => pure (.value value true)
  | .range fieldId start finish => do
      if !validStringRange start finish then throw (.invalidRange start finish)
      match ← read fieldId with
      | .notEvaluated => pure (.value "" false)
      | .unknown cause => pure (.unknown cause)
      | .value value given =>
          if utf16CodeUnitLength value < finish then pure (.value "" given)
          else match utf16CodeUnitSlice? value (start - 1) finish with
            | some selected => pure (.value selected given)
            | none => throw (.unalignedUtf16Range fieldId start finish)
  | .concat left right => do
      let left ← left.evalOperandWith phase read
      match phase, left with
      | .computation, .unknown cause => pure (.unknown cause)
      | _, _ => pure (concatOperands left (← right.evalOperandWith phase read))

/-- Root storage consumes the same expression result without needing validation's omission flag. -/
def eval (context : StringComputationContext) (expression : StringExpr FieldId) :
    Except StringComputationFault StringTerm := do
  pure (StringTerm.ofOperand (← expression.evalOperandWith .computation
    (readOperandAt .computation context.read)))

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
  /-- A reached guard runtime failure has no attempted text and poisons dependents; the retained
  comparison grid distinguishes it from an inherited poison by its target value-error code. -/
  | invalidNoValue
  | noValue
  | accepted (value : StoredString)
  | errored (attempted : StoredString) (cause : StringTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Reduced Custom target validation accepts the attempted payload without calling the registered
validator or ordinary String format policy (spec/06 A.3, spec/09 §11). -/
def StringStore.uncheckedTarget : StringStore → StringTargetOutcome
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .produced value => .accepted value

/-- Apply the declaration-owned basic String clauses and optional prepared matcher to a root write attempt. Checking may normalize CRLF for pattern and length measurement, but an accepted or rejected result retains the exact attempted payload. No-value and poison bypass target validation unchanged. -/
def StringFieldPolicy.checkTargetWithPattern (policy : StringFieldPolicy)
    (wholeValueMatches? : Option (String → Bool)) :
    StringStore → StringTargetOutcome
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .produced attempted =>
      match policy.checkTextWithPattern wholeValueMatches? attempted.text with
      | .ok _ => .accepted attempted
      | .error cause => .errored attempted cause

/-- The target's reduced-check regime is part of a resolved computation, including erased tables. -/
inductive StringTargetRegime where
  | ordinary
  | custom
  deriving Repr, DecidableEq

def StringTargetRegime.check (regime : StringTargetRegime) (policy : StringFieldPolicy)
    (matcher : Option (String → Bool)) (store : StringStore) : StringTargetOutcome :=
  match regime with
  | .ordinary => policy.checkTargetWithPattern matcher store
  | .custom => store.uncheckedTarget

/-- The ordinary no-pattern target specialization retained by the resolved computation and evidence boundaries. -/
def StringFieldPolicy.checkTarget (policy : StringFieldPolicy) :
    StringStore → StringTargetOutcome :=
  policy.checkTargetWithPattern none

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
  | .noValue | .invalidNoValue | .poison _ => StringDelta.projectNoValue prior

/-- Value-only view after applying a computation result. It deliberately does not claim whether the resulting empty target instance is absent or present-empty. -/
def appliedValue : StringTargetOutcome → Option StoredString
  | .accepted value => some value
  | .noValue | .invalidNoValue | .errored _ _ | .poison _ => none

end StringTargetOutcome

namespace StringStore

/-- Preserve the original pre-target-check delta API without manufacturing a post-check accepted outcome. -/
def projectDelta (result : StringStore) (prior : PriorStringTarget) : Option StringDelta :=
  match result with
  | .produced value => StringDelta.projectValue value prior
  | .noValue | .poison _ => StringDelta.projectNoValue prior

end StringStore

end A12Kernel
