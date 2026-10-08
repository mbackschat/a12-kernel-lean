import A12Kernel.Elaboration.ErrorTextRowParameter

/-! # Locks on the error-text row-index parameter

The star rule and the resolve stage's class are measured with four separating rows and a plain-message
control; the availability gate, the shared code's second cause, the last stage's split and the
escaped-dollar trigger are source-derived
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-error-text-row-parameter)).
-/

namespace A12Kernel.Conformance.ErrorTextRowParameter

open A12Kernel

private def plain : RowParameterSpelling := {}
private def withSemanticIndex : RowParameterSpelling := { hasSemanticIndex := true }

private def key? (profile : GroupReferenceProfile) (spelling : RowParameterSpelling) :
    Option String :=
  (rowParameterRefusal profile spelling).map KernelStaticDiagnostic.kernelCode

private def keys (containsDollar conditionParses : Bool)
    (others : List KernelStaticDiagnostic) (profile : GroupReferenceProfile)
    (spelling : RowParameterSpelling) : List String :=
  (errorTextFindings containsDollar conditionParses others profile spelling).map
    KernelStaticDiagnostic.kernelCode

/- **The measured matrix.** A group referenced without a star admits the parameter; the same group
   reached only through a star refuses; adding an unstarred reference back to that condition admits
   it again, which is what makes the rule existential; and a path naming no group draws the resolve
   stage's own class. -/
example :
    key? {} plain = none ∧
      key? { referencedWithoutStar := false } plain = some "ITER_PARAM_WITH_STARREFERENCE" ∧
      key? { resolvesToGroup := false } plain = some "INVALID_GROUP" := by
  native_decide

/- **The shared code carries two causes.** Both stages report it, and the second is reachable with a
   path that does resolve — so a consumer cannot read the cause from the code. -/
example :
    key? { resolvesToGroup := false } plain = some "INVALID_GROUP" ∧
      key? { admittedByCondition := false } plain = some "INVALID_GROUP" ∧
      key? { resolvesToGroup := false, admittedByCondition := true } plain =
        some "INVALID_GROUP" := by
  native_decide

/- **The last stage's class follows the parameter's spelling.** One inconsistency, two codes, and the
   only thing that moved between the rows is whether a semantic index was written. -/
example :
    key? { iterationConsistent := false } withSemanticIndex =
        some "INVALID_USE_OF_SEMANTIC_INDEX" ∧
      key? { iterationConsistent := false } plain = some "INVALID_USE_OF_ITERATION_PARAM" ∧
      key? {} withSemanticIndex = none := by
  native_decide

/- **The stages are ordered.** Four profiles, each clearing one more stage than the last, walking the
   cascade top to bottom. -/
example :
    key? { resolvesToGroup := false, admittedByCondition := false,
           referencedWithoutStar := false, iterationConsistent := false } plain =
        some "INVALID_GROUP" ∧
      key? { admittedByCondition := false, referencedWithoutStar := false,
             iterationConsistent := false } plain = some "INVALID_GROUP" ∧
      key? { referencedWithoutStar := false, iterationConsistent := false } plain =
        some "ITER_PARAM_WITH_STARREFERENCE" ∧
      key? { iterationConsistent := false } plain = some "INVALID_USE_OF_ITERATION_PARAM" := by
  native_decide

/- **An unparseable condition reports that it could not check, and admits the parameter it would have
   refused.** The pair differs in the parse flag alone, and the second row's empty parameter list is
   silence rather than approval. -/
example :
    keys true true [] { referencedWithoutStar := false } plain =
        ["ITER_PARAM_WITH_STARREFERENCE"] ∧
      keys true false [] { referencedWithoutStar := false } plain = ["INVALID_CONDITION"] ∧
      keys true false [.invalidFieldInParameter] { referencedWithoutStar := false } plain =
        ["INVALID_CONDITION", "INVALID_FIELD_IN_PARAMETER"] := by
  native_decide

/- **The trigger is the dollar character.** A message carrying one — even an escaped literal, which
   the Kernel's own source records as a false positive — drags the condition in; a message with none
   is silent over the identical broken condition and profile. -/
example :
    keys false false [] { referencedWithoutStar := false } plain = [] ∧
      keys true false [] {} plain = ["INVALID_CONDITION"] ∧
      messageNeedsCondition true = true ∧
      messageNeedsCondition false = false := by
  native_decide

end A12Kernel.Conformance.ErrorTextRowParameter
