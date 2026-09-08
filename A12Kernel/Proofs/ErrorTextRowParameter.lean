import A12Kernel.Elaboration.ErrorTextRowParameter

/-! # Laws of the error-text row-index parameter

Four results carry the family. The first two stages share one code, so that code does not identify
its cause. The star rule is existential over the condition's references rather than universal, so an
unstarred reference beside a starred one admits. The last stage's code follows the parameter's own
spelling and not the failure, so the two codes there describe one condition. And the availability
gate turns the whole cascade off, so an unparseable condition admits every parameter it would
otherwise refuse while separately reporting that it could not check them.
-/

namespace A12Kernel

/-- **The shared code is many-to-one.** A path naming nothing and a path naming a group the condition
does not reach report the same class, so a repair tool cannot read the cause off the code. -/
theorem rowParameterRefusal_invalidGroup_two_causes (spelling : RowParameterSpelling) :
    rowParameterRefusal { resolvesToGroup := false } spelling =
        some .invalidGroupInParameter ∧
      rowParameterRefusal { admittedByCondition := false } spelling =
        some .invalidGroupInParameter := by
  constructor <;> simp [rowParameterRefusal]

/-- **The star rule is existential.** Only the `referencedWithoutStar` flag decides it, so a condition
holding an unstarred reference admits the parameter whatever else it holds. -/
theorem rowParameterRefusal_star_rule (spelling : RowParameterSpelling)
    (profile : GroupReferenceProfile) (hresolve : profile.resolvesToGroup = true)
    (hadmit : profile.admittedByCondition = true) (hiter : profile.iterationConsistent = true) :
    rowParameterRefusal profile spelling =
      (if profile.referencedWithoutStar then none else some .iterParamWithStarReference) := by
  simp only [rowParameterRefusal, hresolve, hadmit, hiter]
  cases profile.referencedWithoutStar <;> simp

/-- **The last stage's code follows the spelling, not the failure.** One inconsistency, two codes,
chosen by whether the parameter wrote a semantic index — so the two classes do not name two
conditions. -/
theorem rowParameterRefusal_last_stage_by_spelling :
    rowParameterRefusal { iterationConsistent := false } { hasSemanticIndex := true } =
        some .invalidUseOfSemanticIndex ∧
      rowParameterRefusal { iterationConsistent := false } { hasSemanticIndex := false } =
        some .invalidUseOfIterationParam :=
  ⟨rfl, rfl⟩

/-- The stages are ordered, so an earlier failure hides every later one. -/
theorem rowParameterRefusal_first_match (spelling : RowParameterSpelling) :
    rowParameterRefusal
      { resolvesToGroup := false, admittedByCondition := false,
        referencedWithoutStar := false, iterationConsistent := false } spelling =
      some .invalidGroupInParameter := by
  simp [rowParameterRefusal]

/-- **No parsed condition admits everything.** The cascade is not run at all, so a parameter that
would draw any of the four classes is silently accepted. -/
theorem rowParameterOutcome_unavailable_admits (profile : GroupReferenceProfile)
    (spelling : RowParameterSpelling) : rowParameterOutcome false profile spelling = none := by
  simp [rowParameterOutcome]

/-- **The condition finding accumulates.** Every finding from a check that does not need the
condition survives beside it, which is the Kernel's deliberate "continue with all other checks"
behaviour and the reason this returns a list. -/
theorem errorTextFindings_accumulates (others : List KernelStaticDiagnostic)
    (profile : GroupReferenceProfile) (spelling : RowParameterSpelling) :
    errorTextFindings true false others profile spelling =
      .errorTextInvalidCondition :: others := by
  simp [errorTextFindings, rowParameterOutcome, messageNeedsCondition]

/-- And the parameter list beside it is empty for the *same* reason the condition finding exists —
never because the parameters were examined and passed. -/
theorem errorTextFindings_unparsed_admits_parameter (profile : GroupReferenceProfile)
    (spelling : RowParameterSpelling) :
    errorTextFindings true false [] profile spelling = [.errorTextInvalidCondition] := by
  simp [errorTextFindings, rowParameterOutcome, messageNeedsCondition]

/-- **A message with no dollar is never checked against the condition**, so it draws no condition
finding however broken that condition is — and the cascade is skipped for the same reason, leaving
only whatever the condition-independent checks found. -/
theorem errorTextFindings_no_dollar_silent (conditionParses : Bool)
    (others : List KernelStaticDiagnostic) (profile : GroupReferenceProfile)
    (spelling : RowParameterSpelling) :
    errorTextFindings false conditionParses others profile spelling = others := by
  simp [errorTextFindings, rowParameterOutcome, messageNeedsCondition]

/-- With a parsed condition the findings are the others plus the cascade's. -/
theorem errorTextFindings_parsed_is_cascade (others : List KernelStaticDiagnostic)
    (profile : GroupReferenceProfile) (spelling : RowParameterSpelling) :
    errorTextFindings true true others profile spelling =
      others ++ (rowParameterRefusal profile spelling).toList := by
  simp [errorTextFindings, rowParameterOutcome, messageNeedsCondition]

end A12Kernel
