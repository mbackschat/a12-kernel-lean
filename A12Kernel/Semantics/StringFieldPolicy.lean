import A12Kernel.Semantics.Observation

/-! # Declaration-owned ordinary String formal policy -/

namespace A12Kernel

/-- The ordinary String declaration facts needed by scalar formal checking. Pattern matching remains a separate injected capability. -/
structure StringFieldPolicy where
  lineBreaksPermitted : Bool := false
  minLength : Option Nat := none
  maxLength : Option Nat := none
  deriving Repr, DecidableEq

/-- The exact first failing clause retained before the current checked-cell boundary projects all local String-format failures to `declaredConstraint`. -/
inductive StringFieldError where
  | lineBreak
  | tooShort
  | tooLong
  deriving Repr, DecidableEq, BEq

namespace StringFieldError

def toBaseFormalCause (_error : StringFieldError) : BaseFormalCause :=
  .declaredConstraint

end StringFieldError

namespace StringFieldPolicy

/-- Check one non-custom, non-Enumeration String exactly once: empty bypasses format checks, forbidden CR/LF is detected on raw text, and admitted text is normalized before UTF-16 min/max measurement. -/
def checkText (policy : StringFieldPolicy) (text : String) :
    Except StringFieldError (Option String) :=
  if text.isEmpty then
    .ok none
  else if !policy.lineBreaksPermitted && containsLineBreak text then
    .error .lineBreak
  else
    let normalized := normalizeEvaluatedString text
    let length := utf16CodeUnitLength normalized
    match policy.minLength with
    | some minimum =>
        if 0 < minimum && length < minimum then
          .error .tooShort
        else
          match policy.maxLength with
          | some maximum =>
              if 0 < maximum && maximum < length then
                .error .tooLong
              else
                .ok (some normalized)
          | none => .ok (some normalized)
    | none =>
        match policy.maxLength with
        | some maximum =>
            if 0 < maximum && maximum < length then
              .error .tooLong
            else
              .ok (some normalized)
        | none => .ok (some normalized)

def minimumExceedsMaximum (policy : StringFieldPolicy) : Bool :=
  match policy.minLength, policy.maxLength with
  | some minimum, some maximum => maximum < minimum
  | _, _ => false

def lineBreakMaximumInvalid (policy : StringFieldPolicy) : Bool :=
  policy.lineBreaksPermitted && policy.maxLength == some 1

/-- Lift ordinary String checking into the heterogeneous scalar domain. -/
def classifyValue (policy : StringFieldPolicy) :
    Value → Except BaseFormalCause (Option Value)
  | .str text =>
      match policy.checkText text with
      | .ok none => .ok none
      | .ok (some checked) => .ok (some (.str checked))
      | .error error => .error error.toBaseFormalCause
  | _ => .error .malformed

/-- Apply declaration-owned ordinary String policy through the shared checked-cell constructor. -/
def checkRaw (policy : StringFieldPolicy) (raw : RawCell) : CheckedCell :=
  checkRawCellWith policy.classifyValue raw

end StringFieldPolicy

end A12Kernel
