import A12Kernel.Semantics.ValueFormalCheck
import A12Kernel.Semantics.NumericInput

/-! # Locks on the universal formal pre-check

Each case below fixes one step of the pipeline against the reading a consumer would otherwise adopt: that the declaration's cascade runs first, that a declared maximum is the only length gate, that normalisation happens before the cascade sees the text, or that switching value validation off is merely a pass.

The composition cases use the Number formal-read cascade as the declaration stage, which is the point of parameterising the pipeline: the Number capsule is unchanged and gains its missing prefix.
-/

namespace A12Kernel.Conformance.ValueFormalCheck

open A12Kernel

/-- A permissive charset, so a case that is not about the charset cannot accidentally trip it. -/
private def anyCharset : ValueFormalEnvironment := { charsetAdmits := fun _ => true }

/-- A charset that refuses one specific grapheme, standing in for a model's declared restriction. -/
private def noExclamation : ValueFormalEnvironment :=
  { charsetAdmits := fun value => !(value.contains '!') }

/-- The Number formal-read cascade on an integer declaration, applied to a fixed admitted value. -/
private def numberCheck (constraints : NumericTargetConstraints) : Option NumericFormalReadError :=
  match constraints.checkFormalRead { scale := 0, signed := true } (.decimal { unscaled := 42, scale := 0 }) with
  | .error error => some error
  | .ok _ => none

/- The pre-check cases are about which text reaches the declaration stage, not about parsing it, so
   this stand-in ignores the text; the case that locks *which* text a stage receives uses
   `lengthReportingStage` instead, because a stage that ignores its argument cannot witness that
   distinction at all. -/
private def numberStage (_value : String) : Option NumericFormalReadError :=
  numberCheck {}

/-- Reports the length of the text it is handed, which is what makes the raw-versus-normalised
choice observable: a CRLF counts twice before normalisation and once after. -/
private def lengthReportingStage (value : String) : Option Nat := some value.length

/- The pre-check runs before the declaration's cascade, so a value that fails both reports the
   pre-check's code. The twin differs only in the leading blank and reaches the cascade. -/
example :
    valueFormalCheck noExclamation numberStage " 42" = .refused .leadingBlank ∧
      valueFormalCheck noExclamation numberStage "42" = .admitted "42" := by
  native_decide

/- Order inside the pre-check is itself observable: a value that breaches the charset *and* opens
   with a blank reports the charset, because that test is first. -/
example :
    valueFormalCheck noExclamation numberStage " !" = .refused .characterNotInCharset ∧
      valueFormalCheck noExclamation numberStage " x" = .refused .leadingBlank := by
  native_decide

/- The trailing-blank test is separate from the leading one and carries its own code, so a consumer
   cannot trim both ends under one refusal — and the leading test runs first, which only a value
   blanked at both ends can witness. -/
example :
    valueFormalCheck anyCharset numberStage "x " = .refused .trailingBlank ∧
      valueFormalCheck anyCharset numberStage " x " = .refused .leadingBlank ∧
      UniversalFormalRefusal.leadingBlank.errorCode ≠
        UniversalFormalRefusal.trailingBlank.errorCode := by
  native_decide

/- The technical ceiling is not a declared maximum: it is fixed, it applies with no declaration
   saying anything about length, and it reports its own code. -/
example :
    maximumStoredValueLength = 99999 ∧
      valueFormalCheck anyCharset numberStage (String.ofList (List.replicate 100000 'x')) =
        .refused .valueTooLong ∧
      valueFormalCheck anyCharset numberStage (String.ofList (List.replicate 99999 'x')) =
        .admitted (String.ofList (List.replicate 99999 'x')) := by
  native_decide

/- The ceiling counts UTF-16 code units, as the Kernel's host string length does: one
   supplementary character fills two, so 99,998 letters and one emoji are over the ceiling while
   99,997 letters and one emoji are not, although both are under it in Unicode scalars. -/
example :
    valueFormalCheck anyCharset numberStage (String.ofList (List.replicate 99998 'x') ++ "😀") =
        .refused .valueTooLong ∧
      valueFormalCheck anyCharset numberStage (String.ofList (List.replicate 99997 'x') ++ "😀") =
        .admitted (String.ofList (List.replicate 99997 'x') ++ "😀") := by
  native_decide

/- Switching value validation off ends the pipeline before every later step, including the technical
   ceiling — so an over-long value is stored as authored rather than refused. This is the arm a
   consumer loses by keeping only the String cascade's own copy of the switch. -/
example :
    valueFormalCheck { anyCharset with skipValueValidation := true } numberStage " ! " =
        .uncheckedPassthrough " ! " ∧
      valueFormalCheck { noExclamation with skipValueValidation := true } numberStage "!" =
        .uncheckedPassthrough "!" ∧
      valueFormalCheck { anyCharset with skipValueValidation := true } numberStage
          (String.ofList (List.replicate 100000 'x')) =
        .uncheckedPassthrough (String.ofList (List.replicate 100000 'x')) := by
  native_decide

/- Normalisation collapses `\r\n` only: a lone `\r` survives, so this is not a general line-ending
   normalisation and does not reduce `\r\r\n` to a single break. -/
example :
    normalizeLinebreaks "a\r\nb" = "a\nb" ∧
      normalizeLinebreaks "a\rb" = "a\rb" ∧
      normalizeLinebreaks "a\nb" = "a\nb" ∧
      normalizeLinebreaks "a\r\r\nb" = "a\r\nb" ∧
      valueFormalCheck anyCharset numberStage "a\r\nb" = .admitted "a\nb" := by
  native_decide

/- The declaration's cascade receives the text **as authored** while the stored value is normalised,
   so on a value carrying one CRLF the two differ by exactly one character. Handing the stage the
   normalised text instead is the silent reimplementation error this case exists to catch, and only a
   stage that reads its argument can witness it. -/
example :
    valueFormalCheck anyCharset lengthReportingStage "a\r\nb" = .refusedByDeclaration 4 ∧
      ("a\r\nb" : String).length = 4 ∧ (normalizeLinebreaks "a\r\nb").length = 3 := by
  native_decide

/- The composition is real rather than decorative: the declaration's own refusal travels out under
   its own constructor, distinct from every pre-check refusal, and keeps its own code. -/
example :
    valueFormalCheck anyCharset
        (fun _ => numberCheck { maximum := some 1 }) "42" =
      .refusedByDeclaration .aboveMaximum := by
  native_decide

/- Every pre-check code is distinct, so the four steps stay separable for a consumer switching on
   the code alone. -/
example :
    (UniversalFormalRefusal.all.map (·.errorCode)).eraseDups.length =
      UniversalFormalRefusal.all.length := by
  native_decide

end A12Kernel.Conformance.ValueFormalCheck
