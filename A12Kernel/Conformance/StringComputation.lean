import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Conformance.StringComputation — direct String computation locks -/

namespace A12Kernel.Conformance.StringComputation

open A12Kernel

private def valueOf : Except ε α → Option α
  | .ok value => some value
  | .error _ => none

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def sourceId : FieldId := 1
private def otherId : FieldId := 2

private def checkedString (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (source other : CheckedCell) : StringComputationContext where
  read field := if field == sourceId then source else if field == otherId then other else checkedString .empty

private def rawContext (source other : RawCell) : StringComputationContext :=
  context (checkedString source) (checkedString other)

private def copySource : StringExpr := .field sourceId
private def sourceThenSuffix : StringExpr := .concat (.field sourceId) (.literal "-X")
private def prefixThenSource : StringExpr := .concat (.literal "X-") (.field sourceId)
private def sourceThenOther : StringExpr := .concat (.field sourceId) (.field otherId)
private def sourceThenOtherThenSuffix : StringExpr :=
  .concat (.concat (.field sourceId) (.field otherId)) (.literal "-X")

private def delta (expression : StringExpr) (computationContext : StringComputationContext)
    (prior : PriorStringTarget) : Except StringComputationFault (Option StringDelta) := do
  let result ← expression.evaluate computationContext
  pure (result.projectDelta prior)

private def storedSeed : StoredString := ⟨"SEED", by decide⟩
private def storedReference : StoredString := ⟨"REF-42", by decide⟩
private def storedSuffix : StoredString := ⟨"-X", by decide⟩
private def storedPrefix : StoredString := ⟨"X-", by decide⟩

example : valueOf (copySource.eval (rawContext (.parsed (.str "REF-42")) .empty)) =
    some (.text "REF-42") := by
  decide

example : valueOf (copySource.evaluate (rawContext (.parsed (.str "REF-42")) .empty)) =
    some (.produced storedReference) := by
  decide

example : valueOf (delta copySource (rawContext (.parsed (.str "REF-42")) .empty)
    (.filled storedSeed)) = some (some (.value storedReference)) := by
  decide

example : valueOf (delta copySource (rawContext (.parsed (.str "REF-42")) .empty)
    (.filled storedReference)) = some none := by
  decide

example : valueOf (copySource.eval (rawContext .empty .empty)) = some .noValue := by
  decide

example : valueOf (copySource.evaluate (rawContext .empty .empty)) = some .noValue := by
  decide

example : valueOf (delta copySource (rawContext .empty .empty) (.filled storedSeed)) =
    some (some .cleared) := by
  decide

example : valueOf (delta copySource (rawContext .empty .empty) .empty) = some none := by
  decide

example : valueOf (sourceThenSuffix.eval (rawContext .empty .empty)) = some (.text "-X") := by
  decide

example : valueOf (sourceThenSuffix.evaluate (rawContext .empty .empty)) =
    some (.produced storedSuffix) := by
  decide

example : valueOf (delta sourceThenSuffix (rawContext .empty .empty) .empty) =
    some (some (.value storedSuffix)) := by
  decide

/- The empty contribution is symmetric; this guards the mechanism beyond the captured suffix direction. -/
example : valueOf (prefixThenSource.evaluate (rawContext .empty .empty)) =
    some (.produced storedPrefix) := by
  decide

/- Concatenation evaluates, but a final empty text is still no stored value. -/
example : valueOf (sourceThenOther.evaluate
    (rawContext (.parsed (.str "REF-42")) .empty)) = some (.produced storedReference) := by
  decide

example : valueOf (sourceThenOther.eval (rawContext .empty .empty)) = some (.text "") := by
  decide

example : valueOf (sourceThenOther.evaluate (rawContext .empty .empty)) = some .noValue := by
  decide

example : valueOf (delta sourceThenOther (rawContext .empty .empty) (.filled storedSeed)) =
    some (some .cleared) := by
  decide

example : valueOf (delta sourceThenOther (rawContext .empty .empty) .empty) = some none := by
  decide

/- Nested evaluation keeps the same empty-contribution mechanism instead of treating an all-empty inner concatenation as a missing outer term. -/
example : valueOf (sourceThenOtherThenSuffix.evaluate (rawContext .empty .empty)) =
    some (.produced storedSuffix) := by
  decide

/- Requiredness is validation-scoped and does not turn an otherwise empty computation read into poison. -/
example : valueOf (copySource.evaluate
    (context ((checkedString .empty).withFinding .required) (checkedString .empty))) = some .noValue := by
  decide

example : valueOf (copySource.evaluate (rawContext (.rejected .malformed) .empty)) =
    some (.poison .malformed) := by
  decide

example : valueOf (delta copySource (rawContext (.rejected .malformed) .empty)
    (.filled storedSeed)) = some (some .cleared) := by
  decide

/- A poisoned left read prevents a wrong-kind right read from surfacing as a context fault. -/
example : valueOf ((StringExpr.concat (.field sourceId) (.field otherId)).evaluate {
    read field :=
      if field == sourceId then checkedString (.rejected .malformed)
      else formalCheck { kind := .number { scale := 0, signed := true } }
        (.parsed (.num 1)) }) = some (.poison .malformed) := by
  decide

/- A clean empty left operand does not hide a poisoned right read. -/
example : valueOf (sourceThenOther.evaluate
    (rawContext .empty (.rejected .malformed))) = some (.poison .malformed) := by
  decide

/- A low-level context carrying the wrong parsed kind fails closed instead of becoming empty or poison. -/
example : errorOf (copySource.evaluate
    (context (formalCheck { kind := .number { scale := 0, signed := true } }
      (.parsed (.num 1))) (checkedString .empty))) =
    some (.fieldKindMismatch sourceId) := by
  decide

/- A clean missing contribution can preserve the final store decision even though it is not an identity at the intermediate expression-result boundary. -/
example : StringTerm.concat .noValue .noValue != .noValue := by
  decide

example : (StringTerm.concat .noValue .noValue).store = StringTerm.noValue.store := by
  decide

end A12Kernel.Conformance.StringComputation
