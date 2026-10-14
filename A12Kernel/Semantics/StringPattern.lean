import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Semantics.StringPattern — resolved whole-value pattern conditions

This capsule begins after an authored pattern has passed Java compilation and the kernel's additional admission gate. The admitted pattern is injected as a pure whole-value matcher, keeping Java `Pattern` compilation and syntax outside Lean while preserving the phase-specific semantics that consume its result.
-/

namespace A12Kernel

/-- The two admitted String-pattern condition operators. There is no generic condition negation. -/
inductive StringPatternOp where
  | matched
  | violated
  deriving Repr, DecidableEq

namespace StringPatternOp

/-- Whether this operator fires for the matcher's Boolean result. -/
def acceptsMatchResult (op : StringPatternOp) (matchedResult : Bool) : Bool :=
  match op with
  | .matched => matchedResult
  | .violated => !matchedResult

/-- Consume one classified checked String with an already-admitted whole-value matcher. Empty input is not evaluated, formal unavailability remains unknown, and every firing is VALUE-typed because a pattern condition never substitutes for missing input. -/
def evalResolved (op : StringPatternOp) (wholeValueMatches : String → Bool) :
    SimpleComparisonOperand String → Verdict
  | .notEvaluated => .notFired
  | .unknown _ => .unknown
  | .value actual _ =>
      if op.acceptsMatchResult (wholeValueMatches actual) then .fired .value else .notFired

/-- Computation consumes the same match decision but retains a reached formal cause as poison,
as required by the shared computation-condition phase contract. -/
def evalComputationResolved (op : StringPatternOp) (wholeValueMatches : String → Bool) :
    SimpleComparisonOperand String → ComputationConditionResult
  | .notEvaluated => .notTrue
  | .unknown cause => .poison cause
  | .value actual _ =>
      if op.acceptsMatchResult (wholeValueMatches actual) then .holds else .notTrue

end StringPatternOp

/-- What a host pattern compiler answers for one source. `rejected` is Java's own syntax verdict;
`unsupported` is the supplied compiler's limit, so a Java-valid source it cannot execute is never
reported as the Kernel's invalid-pattern class. -/
inductive PatternCompilation where
  | compiled (wholeValueMatches : String → Bool)
  | rejected
  | unsupported

def PatternCompilation.matcher? : PatternCompilation → Option (String → Bool)
  | .compiled wholeValueMatches => some wholeValueMatches
  | .rejected | .unsupported => none

/-- A pure host capability returning the whole-value matcher compiled from that exact source.
Construction-time caching remains the caller's responsibility. -/
abbrev StringPatternCompiler := String → PatternCompilation

/-- `hostUnsupported` carries no Kernel class: the Kernel's own compiler would have answered. -/
inductive PatternAdmissionError where
  | javaSyntax
  | kernelRestriction
  | hostUnsupported
  deriving Repr, DecidableEq

inductive PatternAdmission where
  | admitted
  | rejected (error : PatternAdmissionError)
  deriving Repr, DecidableEq

private def isForbiddenEscapeLetter (character : Char) : Bool :=
  character == 'A' || character == 'G' || character == 'Z' ||
    character == 'z' || character == 'a' || character == 'e' ||
    character == 'p' || character == 'Q' ||
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

/-- Reject a second unescaped class opener before the next `]`. Escaping is intentionally source-local: an immediately preceding backslash protects a following opener, but **not** a closer — any `]` ends the scan, so `[a\][b]]` is admitted although Java reads its second `[` as nested ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-regex-operands)). -/
private def containsNestedClassOpen (source : List Char) : Bool :=
  let rec scan (insideClass previousWasBackslash : Bool) : List Char → Bool
    | [] => false
    | character :: remaining =>
        let isUnescaped := !previousWasBackslash
        if character == '[' && isUnescaped then
          if insideClass then true else scan true false remaining
        else if character == ']' then
          scan false false remaining
        else
          scan insideClass (character == '\\') remaining
  scan false false source

/-- The documented post-compilation source gate. It is a bounded exclusion predicate, not an invented complete regex grammar. -/
def kernelPatternSourceAllowed (source : String) : Bool :=
  !containsForbiddenPatternSequence source.toList &&
    !containsNestedClassOpen source.toList

/-- Classify the two admission stages while preserving compiler-rejection precedence. -/
def classifyStringPattern (compilePattern : StringPatternCompiler)
    (source : String) : PatternAdmission :=
  match compilePattern source with
  | .rejected => .rejected .javaSyntax
  | .unsupported => .rejected .hostUnsupported
  | .compiled _ =>
      if kernelPatternSourceAllowed source then .admitted
      else .rejected .kernelRestriction

/-- A pattern source paired with the exact matcher returned by the injected compiler and the post-compilation kernel admission fact. -/
structure AdmittedStringPattern (compilePattern : StringPatternCompiler) where
  source : String
  wholeValueMatches : String → Bool
  compiledSource :
    compilePattern source = .compiled wholeValueMatches
  kernelSourceAllowed : kernelPatternSourceAllowed source = true

/-- Construct the proof-bearing pattern capability or retain the exact failed stage. -/
def admitStringPattern (compilePattern : StringPatternCompiler)
    (source : String) :
    Except PatternAdmissionError (AdmittedStringPattern compilePattern) :=
  match hCompiled : compilePattern source with
  | .rejected => .error .javaSyntax
  | .unsupported => .error .hostUnsupported
  | .compiled wholeValueMatches =>
    if hAllowed : kernelPatternSourceAllowed source = true then
      .ok {
        source
        wholeValueMatches
        compiledSource := hCompiled
        kernelSourceAllowed := hAllowed
      }
    else
      .error .kernelRestriction

/-- An admitted empty authored source fails when called, before operand availability is tested
(`RuntimeController.vergleichePatternSTRING`, kernel 30.8.1). Declaration-owned empty patterns
remain inactive and do not enter this condition boundary. -/
inductive StringPatternRuntimeFault where
  | emptySource
  deriving Repr, DecidableEq

def AdmittedStringPattern.checkExecution
    (admitted : AdmittedStringPattern compilePattern) : Except StringPatternRuntimeFault Unit :=
  if admitted.source.isEmpty then .error .emptySource else .ok ()

/-- Admission does not guarantee executable success; preserve failure until the enclosing handler. -/
def AdmittedStringPattern.evalResolved
    (admitted : AdmittedStringPattern compilePattern)
    (op : StringPatternOp)
    (operand : SimpleComparisonOperand String) : Except StringPatternRuntimeFault Verdict :=
  match admitted.checkExecution with
  | .error fault => .error fault
  | .ok () => .ok (op.evalResolved admitted.wholeValueMatches operand)

/-- Computation's formal-input precheck prevents the runtime call on unavailable input;
empty/absent input still reaches it (empty-pattern computation grid, 2026-10-10). -/
def AdmittedStringPattern.evalComputationResolved
    (admitted : AdmittedStringPattern compilePattern)
    (op : StringPatternOp)
    (operand : SimpleComparisonOperand String) : Except StringPatternRuntimeFault ComputationConditionResult :=
  match operand with
  | .unknown cause => .ok (.poison cause)
  | operand => match admitted.checkExecution with
    | .error fault => .error fault
    | .ok () => .ok (op.evalComputationResolved admitted.wholeValueMatches operand)

/-- Keep static rejection and a reached execution failure distinct at the convenience boundary. -/
def evalAdmittedStringPattern (compilePattern : StringPatternCompiler) (source : String)
    (op : StringPatternOp)
    (operand : SimpleComparisonOperand String) : Except (Sum PatternAdmissionError StringPatternRuntimeFault) Verdict :=
  match admitStringPattern compilePattern source with
  | .error error => .error (.inl error)
  | .ok admitted => (admitted.evalResolved op operand).mapError Sum.inr

/-- A prepared pattern keeps the compiler and its exact source-indexed matcher together. -/
structure CompiledStringPattern where
  compilePattern : StringPatternCompiler
  pattern : AdmittedStringPattern compilePattern

instance : Repr CompiledStringPattern where
  reprPrec compiled _ := repr compiled.pattern.source


/-- Evaluate a resolved pattern condition through the same normalized validation-phase String read used by direct equality. The matcher is called only for a present, formally valid, nonempty String. -/
def FlatContext.evalResolvedStringPattern (context : FlatContext)
    (op : StringPatternOp) (field : FlatStringField)
    (wholeValueMatches : String → Bool) : Verdict :=
  op.evalResolved wholeValueMatches
    (context.resolveDirectStringComparisonOperand field)

end A12Kernel
