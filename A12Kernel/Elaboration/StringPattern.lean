import A12Kernel.Semantics.StringPattern

/-! # A12Kernel.Elaboration.StringPattern — checked two-stage pattern admission

The kernel first requires Java-pattern compilation and then applies a finite source gate. Java compilation remains an injected capability: Lean records its Boolean decision but does not reimplement a regex engine. The source scan below is an original character walk over the canonically documented exclusion families, including the separately observed uppercase-`\P` exclusion. Passing this gate is not a JavaScript-portability claim.
-/

namespace A12Kernel

inductive PatternAdmissionError where
  | javaSyntax
  | kernelRestriction
  deriving Repr, DecidableEq

inductive PatternAdmission where
  | admitted
  | rejected (error : PatternAdmissionError)
  deriving Repr, DecidableEq

private def isForbiddenEscapeLetter (character : Char) : Bool :=
  character == 'A' || character == 'G' || character == 'Z' ||
    character == 'z' || character == 'a' || character == 'e' ||
    character == 'p' || character == 'P' || character == 'Q' ||
    character == 'E'

/-- Detect the finite adjacent source forms rejected after Java compilation. This is deliberately a character scanner, not a transcription of the kernel's regular expression. -/
private def containsForbiddenPatternSequence : List Char → Bool
  | first :: second :: remaining =>
      let possessive :=
        (first == '?' || first == '+' || first == '}' || first == '*') &&
          second == '+'
      let forbiddenEscape := first == '\\' && isForbiddenEscapeLetter second
      let forbiddenGroupPrefix :=
        match remaining with
        | third :: _ => first == '(' && second == '?' && (third == '<' || third == '>')
        | [] => false
      possessive || forbiddenEscape || forbiddenGroupPrefix ||
        containsForbiddenPatternSequence (second :: remaining)
  | _ => false

/-- Reject a second unescaped class opener before the first class closes. Escaping is intentionally source-local: an immediately preceding backslash protects the following bracket. -/
private def containsNestedClassOpen (source : List Char) : Bool :=
  let rec scan (insideClass previousWasBackslash : Bool) : List Char → Bool
    | [] => false
    | character :: remaining =>
        let isUnescaped := !previousWasBackslash
        if character == '[' && isUnescaped then
          if insideClass then true else scan true false remaining
        else if character == ']' && isUnescaped then
          scan false false remaining
        else
          scan insideClass (character == '\\') remaining
  scan false false source

/-- The documented post-compilation source gate. It is a bounded exclusion predicate, not an invented complete regex grammar. -/
def kernelPatternSourceAllowed (source : String) : Bool :=
  !containsForbiddenPatternSequence source.toList &&
    !containsNestedClassOpen source.toList

/-- Classify the two admission stages while preserving compiler-rejection precedence. -/
def classifyStringPattern (javaCompiles : String → Bool)
    (source : String) : PatternAdmission :=
  if javaCompiles source then
    if kernelPatternSourceAllowed source then .admitted
    else .rejected .kernelRestriction
  else
    .rejected .javaSyntax

/-- A pattern source carrying both checked admission facts. The function parameter names the injected Java compiler decision under which the certificate was constructed. -/
structure AdmittedStringPattern (javaCompiles : String → Bool) where
  source : String
  javaCompiles_source : javaCompiles source = true
  kernelSourceAllowed : kernelPatternSourceAllowed source = true

/-- Construct the proof-bearing pattern certificate or retain the exact failed stage. -/
def admitStringPattern (javaCompiles : String → Bool)
    (source : String) :
    Except PatternAdmissionError (AdmittedStringPattern javaCompiles) :=
  if hCompiles : javaCompiles source = true then
    if hAllowed : kernelPatternSourceAllowed source = true then
      .ok { source, javaCompiles_source := hCompiles, kernelSourceAllowed := hAllowed }
    else
      .error .kernelRestriction
  else
    .error .javaSyntax

/-- Evaluate only after both admission stages have succeeded. The caller supplies the Java-compatible whole-value matcher compiled from this certificate's source; runtime truth remains owned by the existing resolved consumer. -/
def AdmittedStringPattern.evalResolved (_admitted : AdmittedStringPattern javaCompiles)
    (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (operand : SimpleComparisonOperand String) : Verdict :=
  op.evalResolved wholeValueMatches operand

/-- Convenience boundary for consumers that check and immediately evaluate one source. -/
def evalAdmittedStringPattern (javaCompiles : String → Bool) (source : String)
    (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (operand : SimpleComparisonOperand String) : Except PatternAdmissionError Verdict :=
  match admitStringPattern javaCompiles source with
  | .error error => .error error
  | .ok admitted => .ok (admitted.evalResolved op wholeValueMatches operand)

end A12Kernel
