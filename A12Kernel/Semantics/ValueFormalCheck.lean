import A12Kernel.Semantics.String

/-! # The universal formal pre-check every stored value passes

[`NumericInput.lean`](NumericInput.lean) owns the ordered formal-read cascade a *Number* declaration applies. That cascade is not the first thing a stored value meets: the Kernel runs a type-independent pre-check first, and only reaches the declaration's own cascade when every step of it passes. A consumer that implements the per-type cascade alone reports the wrong refusal for a value that fails earlier, and reports one at all for a value the pre-check would have waved through unchecked.

The pre-check is a first-match-wins sequence like its per-type successors, so the order below is observable and not an implementation detail:

1. **A String declaration that switches value validation off ends the pipeline immediately**, before the length cap and before any conversion. The stored value is passed through as authored. Only a String declaration carries the switch, so this arm is unreachable for every other kind.
2. **A value longer than the technical cap is refused**, whatever the declaration says. The cap counts the authored text in UTF-16 code units, the host string length, so a supplementary character counts two and a CRLF pair counts two even though normalisation later collapses it. This cap is the Kernel's own and has nothing to do with a declared maximum length: the two produce different codes, and a String field declaring `maxLength` still meets this one first.
3. **The charset, then a leading blank, then a trailing blank.** Each is its own code and the first to fire wins, so a value that both opens with a blank and carries an illegal character reports the character.
4. Only then the declaration's own cascade — the Number one, or a String's, or any other kind's.

**Two traps a reimplementer walks into here.**

The per-type cascade receives the value **as authored**, while the value that reaches storage is line-break normalised. Normalisation happens between the two, so a declared length constraint is measured against text that may be shorter than what the charset and blank checks examined. Only `\r\n` collapses, and a lone `\r` survives, so the two lengths differ by exactly the number of CRLF pairs.

The value-validation switch is consulted **twice**, once here and once inside the String cascade, and the two are not redundant. Reaching it here ends the pipeline with no converted value at all; reaching it inside the String cascade returns a pass and lets the conversion run. A consumer that keeps only the inner check produces a converted value where the Kernel produces none.

**Evidence status: `external evidence pending`.** The order and the cap are read from the runtime's own checker; no observation of a running validation is retained for this clause. The charset predicate is caller-supplied: the Kernel resolves it from a grapheme trie with its own concatenation rules, which is a declaration-layer question this clause deliberately does not decide.
-/

namespace A12Kernel

/-- The technical ceiling on any stored value's length in UTF-16 code units, independent of every declaration. A declared maximum is a separate constraint checked later and reported under its own code. -/
def maximumStoredValueLength : Nat := 99999

/-- Whether authored text breaches the technical ceiling. Measured before line-break normalisation, in UTF-16 code units rather than Unicode scalars. -/
def exceedsTechnicalLength (value : String) : Bool :=
  utf16CodeUnitLength value > maximumStoredValueLength

/-- A refusal from the type-independent pre-check, before any declaration's own cascade. -/
inductive UniversalFormalRefusal where
  /-- Longer than the technical ceiling. Distinct from a declared maximum length. -/
  | valueTooLong
  /-- Carries a grapheme outside the model's declared character set. -/
  | characterNotInCharset
  /-- Opens with a blank. -/
  | leadingBlank
  /-- Ends with a blank. -/
  | trailingBlank
  deriving Repr, DecidableEq

namespace UniversalFormalRefusal

/-- The code a `validateFull` consumer reads. -/
def errorCode : UniversalFormalRefusal → String
  | .valueTooLong => "wertZuLang"
  | .characterNotInCharset => "ZeichenNichtImZeichensatz"
  | .leadingBlank => "fuehrendesBlank"
  | .trailingBlank => "nachfolgendesBlank"

/-- Every pre-check refusal, in the order the Kernel tests them. -/
def all : List UniversalFormalRefusal :=
  [.valueTooLong, .characterNotInCharset, .leadingBlank, .trailingBlank]

end UniversalFormalRefusal

/-- What the pre-check needs from the surrounding declaration and model. -/
structure ValueFormalEnvironment where
  /-- Whether the model's declared character set admits the whole value. Caller-supplied: the Kernel
  resolves this from a grapheme trie whose concatenation rules are a declaration-layer question. -/
  charsetAdmits : String → Bool
  /-- Set only by a String declaration that switches value validation off. No other kind can carry
  it, so leaving it false is the correct encoding for every other declaration. -/
  skipValueValidation : Bool := false

/-- The pipeline's outcome for one authored value, parameterised by the declaration's own refusal type so the Number, String, and every later cascade compose with it unchanged. -/
inductive ValueFormalOutcome (TypeRefusal : Type) where
  /-- The String no-value-validation switch ended the pipeline. The value is stored as authored and
  **no conversion runs**, which is what distinguishes this from an ordinary pass. -/
  | uncheckedPassthrough (authored : String)
  /-- The type-independent pre-check refused. -/
  | refused (refusal : UniversalFormalRefusal)
  /-- The pre-check passed and the declaration's own cascade refused. -/
  | refusedByDeclaration (refusal : TypeRefusal)
  /-- Everything passed. The stored value is line-break normalised, unlike the text the cascade saw. -/
  | admitted (stored : String)
  deriving Repr, DecidableEq

/-- Collapse `\r\n` to `\n`, the Kernel's whole normalisation. A lone `\r` is deliberately left alone, so this is not a general line-ending normalisation and does not idempotently reduce `\r\r\n`. -/
def normalizeLinebreaks (value : String) : String :=
  value.replace "\r\n" "\n"

/-- The pre-check's first failing step for a validated value, in the Kernel's order: the technical
length, the charset, a leading blank, a trailing blank. The value-validation switch is the caller's,
since it ends the pipeline before any of these. -/
def universalFormalRefusal? (charsetAdmits : String → Bool) (value : String) :
    Option UniversalFormalRefusal :=
  if exceedsTechnicalLength value then some .valueTooLong
  else if !charsetAdmits value then some .characterNotInCharset
  else if value.startsWith " " then some .leadingBlank
  else if value.endsWith " " then some .trailingBlank
  else none

/-- Run the universal pre-check and, when it passes, the declaration's own cascade.

The `declarationStage` receives the value **as authored**, matching the Kernel: normalisation applies
to the stored result only. Passing the normalised text instead is the single most likely
reimplementation error here, and it is silent whenever no value in the fixture set carries a CRLF. -/
def valueFormalCheck {TypeRefusal : Type}
    (environment : ValueFormalEnvironment)
    (declarationStage : String → Option TypeRefusal)
    (value : String) : ValueFormalOutcome TypeRefusal :=
  if environment.skipValueValidation then
    .uncheckedPassthrough value
  else match universalFormalRefusal? environment.charsetAdmits value with
    | some refusal => .refused refusal
    | none =>
        match declarationStage value with
        | some refusal => .refusedByDeclaration refusal
        | none => .admitted (normalizeLinebreaks value)

end A12Kernel
