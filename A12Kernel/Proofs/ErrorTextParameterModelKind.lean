import A12Kernel.Elaboration.ErrorTextParameterModelKind

/-! # Laws of the model-kind gate over the `#` message parameters

The shadowing law is the one an A12 consumer needs: on an A12 model the two iteration classes are not
merely unobserved but **unreachable**, so a diagnostic corpus from A12 models can never contain them and
a mapping that produces them is wrong rather than incomplete.

The serial parameter's independence from the model kind is proved rather than asserted, because it is the
exception to the rule beside it and an account that generalizes the gate to all three `#` parameters is
the natural mistake.

The suppression asymmetry is what distinguishes the two behaviours observably: a broken condition
silences the serial parameter and leaves the kind refusal standing.
-/

namespace A12Kernel

/-- On an A12 model both iteration parameters report the world, whatever the condition does. -/
theorem hashParameter_a12_is_new_world (iteration : ConditionIteration) :
    hashParameterRefusal .a12 iteration .line = some .parameterInvalidInNewWorld ∧
      hashParameterRefusal .a12 iteration .subScope = some .parameterInvalidInNewWorld :=
  ⟨rfl, rfl⟩

/-- **The shadowing law.** No A12 model reports either iteration class, for any condition and either
parameter — so those classes are unreachable in that world rather than unobserved. -/
theorem noIterationClasses_unreachable_on_a12 (iteration : ConditionIteration)
    (parameter : HashParameter) :
    hashParameterRefusal .a12 iteration parameter ≠ some .noLineIteration ∧
      hashParameterRefusal .a12 iteration parameter ≠ some .noSubScopeIteration := by
  cases parameter <;>
    simp [hashParameterRefusal] <;>
    split <;> simp

/-- **The exception, proved.** The serial parameter's verdict does not depend on the model kind, so the
gate governing its two neighbours does not generalize to it. -/
theorem serialParameter_ignores_model_kind (iteration : ConditionIteration) :
    hashParameterRefusal .hModel iteration .serial =
      hashParameterRefusal .a12 iteration .serial := rfl

/-- **The suppression asymmetry.** An unparsed condition admits the serial parameter while leaving the
A12 refusal of its neighbour standing, which is what makes the two gates observably different rather
than two spellings of one. -/
theorem unparsedCondition_splits_the_hash_parameters (iteration : ConditionIteration)
    (h : iteration.parsed = false) :
    hashParameterRefusal .a12 iteration .serial = none ∧
      hashParameterRefusal .a12 iteration .line = some .parameterInvalidInNewWorld := by
  refine ⟨?_, rfl⟩
  simp [hashParameterRefusal, h]

/-- An unparsed condition also silences both iteration classes on an H-model, so the parsed flag gates
the iteration tests in that world exactly as it gates the serial parameter in both. -/
theorem unparsedCondition_admits_iteration_parameters (iteration : ConditionIteration)
    (h : iteration.parsed = false) :
    hashParameterRefusal .hModel iteration .line = none ∧
      hashParameterRefusal .hModel iteration .subScope = none := by
  constructor <;> simp [hashParameterRefusal, h]

/-- **The gate runs in opposite directions.** The path-spec class is reachable only on an H-model, where
the iteration classes also live, while the world class is reachable only on an A12 model — so neither
kind is the other's superset. -/
theorem pathSpec_and_newWorld_are_opposite (nameCarriesSlash : Bool)
    (iteration : ConditionIteration) :
    pathSpecRefusal .a12 nameCarriesSlash = none ∧
      pathSpecRefusal .hModel true = some .pathSpecNotAllowed ∧
      hashParameterRefusal .hModel iteration .line ≠ some .parameterInvalidInNewWorld := by
  refine ⟨rfl, rfl, ?_⟩
  simp [hashParameterRefusal]

end A12Kernel
