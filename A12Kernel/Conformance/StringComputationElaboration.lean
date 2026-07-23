import A12Kernel.Elaboration.StringComputation

/-! # Checked String-computation expression lowering locks -/

namespace A12Kernel.Conformance.StringComputationElaboration

open A12Kernel

private def source : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Source",
    policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true } }

private def suffix : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Suffix",
    policy := { kind := .string } }

private def amount : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } } }

private def repeatedText : FlatFieldDecl :=
  { id := 3, groupPath := ["Form", "Rows"], name := "Text",
    policy := { kind := .string }, repeatableScope := [10] }

private def target : FlatFieldDecl :=
  { id := 4, groupPath := ["Form"], name := "Target",
    policy := { kind := .string },
    stringPolicy := {
      lineBreaksPermitted := true
      minLength := some 2
      maxLength := some 5 } }

private def model : FlatModel :=
  { fields := [source, suffix, amount, repeatedText, target]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"] }] }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def coreOf
    (result : Except StringComputationElabError (CheckedStringExpr model)) :
    Option StringExpr :=
  result.toOption.map (·.core)

private def errorOf
    (result : Except StringComputationElabError (CheckedStringExpr model)) :
    Option StringComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def operationPolicyOf
    (result : Except StringComputationElabError
      (CheckedStringComputationOperation model)) : Option A12Kernel.StringFieldPolicy :=
  match result with
  | .ok checked => some checked.targetPolicy
  | .error _ => none

private def operationOutcomeOf
    (result : Except StringComputationElabError
      (CheckedStringComputationOperation model))
    (input : RawFlatContext) : Option StringTargetOutcome :=
  match result with
  | .ok checked => (checked.evaluateOutcome input).toOption
  | .error _ => none

private def operationErrorOf {candidateModel : FlatModel}
    (result : Except StringComputationElabError
      (CheckedStringComputationOperation candidateModel)) : Option StringComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def raw (sourceCell suffixCell : RawCell) : RawFlatContext where
  read field :=
    if field = source.id then sourceCell
    else if field = suffix.id then suffixCell
    else .empty

private def storeOf (expression : StringExpr SurfaceFieldPath)
    (input : RawFlatContext) : Option StringStore :=
  match elaborateStringExpr model ["Form"] expression with
  | .error _ => none
  | .ok checked => (checked.evaluate input).toOption

private def normalizedResult : StoredString :=
  { text := "A\nB!", nonempty := by decide }

private def rawCrLfResult : StoredString :=
  { text := "AB\r\nCD", nonempty := by decide }

private def rangeResult : StoredString :=
  { text := "BCD", nonempty := by decide }

/- Copy, decoded literal, and concatenation lower structurally without changing encounter order. -/
example :
    coreOf (elaborateStringExpr model ["Form"]
      (.concat
        (.field (absolute ["Form"] "Source"))
        (.concat (.literal "-") (.field (bare "Suffix"))))) =
      some (.concat (.field source.id)
        (.concat (.literal "-") (.field suffix.id))) := by
  native_decide

/- A legal authored `RangeAsString` retains its 1-based inclusive bounds and resolves only its field leaf. -/
example :
    coreOf (elaborateStringExpr model ["Form"]
      (.range (bare "Source") 2 4)) = some (.range source.id 2 4) := by
  native_decide

/- Field resolution and repeatable-shape rejection precede interval checking. -/
example :
    errorOf (elaborateStringExpr model ["Form"]
      (.range (bare "Missing") 0 3)) =
        some (.resolve (.invalidEntity (bare "Missing"))) ∧
    errorOf (elaborateStringExpr model ["Form"]
      (.range (absolute ["Form", "Rows"] "Text") 0 3)) =
        some (.resolve (.repeatableReference repeatedText.path)) := by
  native_decide

/- Once the field shape resolves, malformed bounds precede String-kind admission. -/
example :
    errorOf (elaborateStringExpr model ["Form"]
      (.range (bare "Amount") 0 3)) = some (.invalidRange 0 3) ∧
    errorOf (elaborateStringExpr model ["Form"]
      (.range (bare "Amount") 3 2)) = some (.invalidRange 3 2) := by
  native_decide

/- The range leaf uses the same declaration-owned String-value gate as a direct copy. -/
example :
    errorOf (elaborateStringExpr model ["Form"]
      (.range (bare "Amount") 1 1)) =
        some (.fieldKindMismatch amount.path .number) := by
  native_decide

/- The checked expression delegates to the existing cached String evaluator. -/
example :
    storeOf
      (.concat (.field (bare "Source")) (.literal "!"))
      (raw (.parsed (.str "A\r\nB")) .empty) =
      some (.produced normalizedResult) := by
  native_decide

/- Two empty field contributions remain an evaluated empty concatenation until the root store clears it. -/
example :
    storeOf
      (.concat (.field (bare "Source")) (.field (bare "Suffix")))
      (raw .presentEmpty .empty) = some .noValue := by
  native_decide

/- Raw cells are checked with the same model policy before the runtime tree reads them. -/
example :
    storeOf (.field (bare "Source"))
      (raw (.parsed (.num 7)) .empty) = some (.poison .malformed) := by
  native_decide

/- Wrong-kind and repeatable reads fail before a runtime expression can be constructed. -/
example :
    errorOf (elaborateStringExpr model ["Form"]
        (.field (bare "Amount"))) =
        some (.fieldKindMismatch amount.path .number) ∧
      errorOf (elaborateStringExpr model ["Form"]
        (.field (absolute ["Form", "Rows"] "Text"))) =
        some (.resolve (.repeatableReference repeatedText.path)) := by
  native_decide

/- Target lowering retains the exact declaration-owned policy, and target checking measures normalized CRLF while preserving the attempted literal payload. -/
example :
    let result := elaborateStringComputationOperation model ["Form"] target.id
      (.literal "AB\r\nCD")
    operationPolicyOf result = some target.stringPolicy ∧
      operationOutcomeOf result (raw .empty .empty) = some (.accepted rawCrLfResult) := by
  native_decide

/- The checked target operation consumes the range result without a parallel target path. -/
example :
    operationOutcomeOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.range (bare "Source") 2 4))
      (raw (.parsed (.str "ABCDE")) .empty) = some (.accepted rangeResult) := by
  native_decide

/- The integrated checked operation rejects self-reference instead of leaving it to runtime evaluation. -/
example :
    operationErrorOf (elaborateStringComputationOperation model ["Form"] target.id
      (.field (bare "Target"))) = some (.targetSelfReference target.id) := by
  native_decide

example :
    operationErrorOf (elaborateStringComputationOperation model ["Form"] target.id
      (.range (bare "Target") 1 1)) = some (.targetSelfReference target.id) := by
  native_decide

/- A non-String target is rejected at the target boundary even when the operation itself is a String literal. -/
example :
    operationErrorOf (elaborateStringComputationOperation model ["Form"] amount.id
      (.literal "TEXT")) = some (.targetKindMismatch amount.path .number) := by
  native_decide

/- Raw, registered-custom, and pattern-bearing String targets require their own target semantics and fail before the ordinary target operation is constructed. -/
example :
    let rawTarget := { target with
      stringValueMode := StringValueMode.raw
      stringPolicy := {
        lineBreaksPermitted := true
        maxLength := some 5 } }
    let rawModel : FlatModel := { fields := [rawTarget] }
    operationErrorOf (elaborateStringComputationOperation rawModel ["Form"]
      rawTarget.id (.literal "TEXT")) = some (.rawStringTarget rawTarget.path) := by
  native_decide

example :
    let customTarget := { target with
      stringPolicy := {}
      customType := some { name := "Code" } }
    let customModel : FlatModel := { fields := [customTarget] }
    operationErrorOf (elaborateStringComputationOperation customModel ["Form"]
      customTarget.id (.literal "TEXT")) =
        some (.customStringTarget customTarget.path) := by
  native_decide

example :
    let patternTarget := { target with
      stringPatternSource := some "[0-9]+" }
    let patternModel : FlatModel := { fields := [patternTarget] }
    operationErrorOf (elaborateStringComputationOperation patternModel ["Form"]
      patternTarget.id (.literal "123")) =
        some (.patternStringTarget patternTarget.path) := by
  native_decide

end A12Kernel.Conformance.StringComputationElaboration
