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
  | pattern
  | tooShort
  | tooLong
  deriving Repr, DecidableEq, BEq

namespace StringFieldError

def toBaseFormalCause (_error : StringFieldError) : BaseFormalCause :=
  .declaredConstraint

end StringFieldError

namespace StringFieldPolicy

/-- Check the positive UTF-16 bounds after every earlier String-format clause has accepted the normalized value. -/
def checkNormalizedLength (policy : StringFieldPolicy) (normalized : String) :
    Except StringFieldError (Option String) :=
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

/-- Check one non-custom, non-Enumeration String exactly once. Empty bypasses every format clause; forbidden CR/LF is detected on raw text; admitted text is normalized; an effective declared pattern is matched against that complete normalized value; and only then are UTF-16 min/max bounds measured. -/
def checkTextWithPattern (policy : StringFieldPolicy)
    (wholeValueMatches? : Option (String → Bool)) (text : String) :
    Except StringFieldError (Option String) :=
  if text.isEmpty then
    .ok none
  else if !policy.lineBreaksPermitted && containsLineBreak text then
    .error .lineBreak
  else
    let normalized := normalizeEvaluatedString text
    match wholeValueMatches? with
    | some wholeValueMatches =>
        if wholeValueMatches normalized then
          policy.checkNormalizedLength normalized
        else
          .error .pattern
    | none => policy.checkNormalizedLength normalized

/-- The ordinary no-pattern specialization. -/
def checkText (policy : StringFieldPolicy) (text : String) :
    Except StringFieldError (Option String) :=
  policy.checkTextWithPattern none text

def minimumExceedsMaximum (policy : StringFieldPolicy) : Bool :=
  match policy.minLength, policy.maxLength with
  | some minimum, some maximum => maximum < minimum
  | _, _ => false

def lineBreakMaximumInvalid (policy : StringFieldPolicy) : Bool :=
  policy.lineBreaksPermitted && policy.maxLength == some 1

/-- Lift ordinary String checking with an optional effective declared matcher into the heterogeneous scalar domain. -/
def classifyValueWithPattern (policy : StringFieldPolicy)
    (wholeValueMatches? : Option (String → Bool)) :
    Value → Except BaseFormalCause (Option Value)
  | .str text =>
      match policy.checkTextWithPattern wholeValueMatches? text with
      | .ok none => .ok none
      | .ok (some checked) => .ok (some (.str checked))
      | .error error => .error error.toBaseFormalCause
  | _ => .error .malformed

/-- The ordinary no-pattern heterogeneous classifier. -/
def classifyValue (policy : StringFieldPolicy) :
    Value → Except BaseFormalCause (Option Value) :=
  policy.classifyValueWithPattern none

/-- Apply declaration-owned ordinary String policy and its effective matcher through the shared checked-cell constructor. -/
def checkRawWithPattern (policy : StringFieldPolicy)
    (wholeValueMatches? : Option (String → Bool)) (raw : RawCell) : CheckedCell :=
  checkRawCellWith (policy.classifyValueWithPattern wholeValueMatches?) raw

/-- Apply declaration-owned ordinary String policy through the shared checked-cell constructor. -/
def checkRaw (policy : StringFieldPolicy) (raw : RawCell) : CheckedCell :=
  policy.checkRawWithPattern none raw

end StringFieldPolicy

end A12Kernel
