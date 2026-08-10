import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.StringContext

/-! # Checked String-computation expression lowering locks -/

namespace A12Kernel.Conformance.StringComputationElaboration

open A12Kernel

private def targetDiagnosticOf
    (error? : Option StringComputationElabError) :
    Option KernelStaticDiagnostic :=
  error?.bind StringComputationElabError.targetDiagnostic?

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

private def digitSource : FlatFieldDecl :=
  {
    id := 10
    groupPath := ["Form"]
    name := "DigitSource"
    policy := { kind := .string }
    stringPatternSource := some asciiDigitsPatternSource
  }

private def customSource : FlatFieldDecl :=
  {
    id := 11
    groupPath := ["Form"]
    name := "CustomSource"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" }
  }

private def preparedModel : FlatModel :=
  { fields := [digitSource, customSource] }

private def preparedRejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def preparedValidator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "accepted" then none else some preparedRejection

private def preparedWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some preparedValidator else none

private def patternInput : FlatFieldDecl :=
  {
    id := 20
    groupPath := ["Form"]
    name := "PatternInput"
    policy := { kind := .string }
  }

private def patternTarget : FlatFieldDecl :=
  {
    id := 21
    groupPath := ["Form"]
    name := "PatternTarget"
    policy := { kind := .string }
    stringPolicy := {
      minLength := some 2
      maxLength := some 4
    }
    stringPatternSource := some "A+"
  }

private def patternTargetModel : FlatModel :=
  { fields := [patternInput, patternTarget] }

private def patternCompiler : StringPatternCompiler := fun source =>
  if source == "A+" then
    some fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    none

private def patternWorld : World :=
  { now := { epochMillis := 0 } }

private def placed (field : FieldId) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw }

private def checkedWith? {candidateModel : FlatModel}
    {compilePattern : StringPatternCompiler}
    (prepared : PreparedFlatStringContext candidateModel compilePattern)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument candidateModel) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private def stringCells (field : FieldId) (value : String) :
    List ClassifiedCellInput :=
  [placed field value (.parsed (.str value))]

private def preparedStore (field : FlatFieldDecl) (value : String) :
    Option StringStore := do
  let prepared ←
    (prepareFlatStringContext preparedWorld builtinStringPatternCompiler
      preparedModel).toOption
  let expression ←
    (elaborateStringExpr preparedModel ["Form"]
      (.field {
        base := .absolute
        groups := ["Form"]
        field := field.name
      })).toOption
  let input ← checkedWith? prepared (stringCells field.id value)
  (expression.evaluate input).toOption

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
    (cells : List ClassifiedCellInput) : Option StringTargetOutcome := do
  let checked ← result.toOption
  let prepared ←
    (prepareFlatStringContext preparedWorld builtinStringPatternCompiler
      model).toOption
  let input ← checkedWith? prepared cells
  (checked.evaluateOutcome prepared.patterns input).toOption

private def operationErrorOf {candidateModel : FlatModel}
    (result : Except StringComputationElabError
      (CheckedStringComputationOperation candidateModel)) : Option StringComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def patternTargetOutcomeOf (expression : StringExpr SurfaceFieldPath)
    (cells : List ClassifiedCellInput) : Option StringTargetOutcome := do
  let checked ←
    (elaborateStringComputationOperation patternTargetModel ["Form"]
      patternTarget.id expression).toOption
  let prepared ←
    (prepareFlatStringContext patternWorld patternCompiler patternTargetModel).toOption
  let input ← checkedWith? prepared cells
  (checked.evaluateOutcome prepared.patterns input).toOption

private def cellFor? (field : FieldId) : RawCell → Option ClassifiedCellInput
  | .empty => none
  | .presentEmpty => some (placed field "" .presentEmpty)
  | .parsed (.str value) => some (placed field value (.parsed (.str value)))
  | .parsed value => some (placed field "wrong-kind" (.parsed value))
  | .rejected cause => some (placed field "rejected" (.rejected cause))

private def cells (sourceCell suffixCell : RawCell) :
    List ClassifiedCellInput :=
  [cellFor? source.id sourceCell, cellFor? suffix.id suffixCell].filterMap id

private def storeOf (expression : StringExpr SurfaceFieldPath)
    (cells : List ClassifiedCellInput) : Option StringStore := do
  let checked ← (elaborateStringExpr model ["Form"] expression).toOption
  let prepared ←
    (prepareFlatStringContext preparedWorld builtinStringPatternCompiler
      model).toOption
  let input ← checkedWith? prepared cells
  (checked.evaluate input).toOption

private def normalizedResult : StoredString :=
  { text := "A\nB!", nonempty := by decide }

private def rawCrLfResult : StoredString :=
  { text := "AB\r\nCD", nonempty := by decide }

private def rangeResult : StoredString :=
  { text := "BCD", nonempty := by decide }

private def digitsResult : StoredString :=
  { text := "123", nonempty := by decide }

private def acceptedResult : StoredString :=
  { text := "accepted", nonempty := by decide }

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

/- `FieldValueAsString` is the typed Number-to-String leaf; it does not widen ordinary String copy syntax. -/
example :
    coreOf (elaborateStringExpr model ["Form"]
      (.fieldValueAsString (bare "Amount"))) =
        some (.fieldValueAsString amount.id) := by
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
      (cells (.parsed (.str "A\r\nB")) .empty) =
      some (.produced normalizedResult) := by
  native_decide

/- Checked String computation consumes both legal prepared source profiles before the existing expression evaluator. -/
example :
    preparedStore digitSource "123" = some (.produced digitsResult) ∧
      preparedStore digitSource "12A" = some (.poison .declaredConstraint) ∧
      preparedStore customSource "accepted" = some (.produced acceptedResult) ∧
      preparedStore customSource "rejected" =
        some (.poison (.registeredCustomValidation preparedRejection)) := by
  native_decide

/- Two empty field contributions remain an evaluated empty concatenation until the root store clears it. -/
example :
    storeOf
      (.concat (.field (bare "Source")) (.field (bare "Suffix")))
      (cells .presentEmpty .empty) = some .noValue := by
  native_decide

/- Raw cells are checked with the same model policy before the runtime tree reads them. -/
example :
    storeOf (.field (bare "Source"))
      (cells (.parsed (.num 7)) .empty) = some (.poison .malformed) := by
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
      operationOutcomeOf result [] = some (.accepted rawCrLfResult) := by
  native_decide

/- The checked target operation consumes the range result without a parallel target path. -/
example :
    operationOutcomeOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.range (bare "Source") 2 4))
      (cells (.parsed (.str "ABCDE")) .empty) = some (.accepted rangeResult) := by
  native_decide

/- The measured direct-copy and root-range target references project to their
exact Kernel class, while an accepted other-field copy remains diagnostic-free. -/
example :
    let direct := operationErrorOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.field (bare "Target")))
    let range := operationErrorOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.range (bare "Target") 1 1))
    let control := operationErrorOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.field (bare "Source")))
    direct = some (.targetSelfReferenceAtRoot target.id) ∧
      range = some (.targetSelfReferenceAtRoot target.id) ∧
      control = none ∧
      targetDiagnosticOf direct = some .errorReferenceToCalculatedField ∧
      targetDiagnosticOf range = some .errorReferenceToCalculatedField ∧
      targetDiagnosticOf control = none := by
  native_decide

/- Wider and malformed target reads retain their local refusal without an exact
Kernel projection because this matrix measured neither branch. -/
example :
    let concatenated := operationErrorOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.concat (.field (bare "Target")) (.literal "X")))
    let invalidRange := operationErrorOf
      (elaborateStringComputationOperation model ["Form"] target.id
        (.range (bare "Target") 0 1))
    concatenated = some (.targetSelfReference target.id) ∧
      invalidRange = some (.invalidRange 0 1) ∧
      targetDiagnosticOf concatenated = none ∧
      targetDiagnosticOf invalidRange = none ∧
      StringComputationElabError.targetDiagnostic?
        (.targetKindMismatch amount.path .number) = none ∧
      StringComputationElabError.targetDiagnostic? .incoherentCore = none := by
  native_decide

/- A non-String target is rejected at the target boundary even when the operation itself is a String literal. -/
example :
    operationErrorOf (elaborateStringComputationOperation model ["Form"] amount.id
      (.literal "TEXT")) = some (.targetKindMismatch amount.path .number) := by
  native_decide

/- Raw and registered-custom String targets require their own target semantics and fail before the ordinary target operation is constructed. -/
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

/- An ordinary pattern-bearing String target remains statically legal. -/
example :
    let patternTarget := { target with
      stringPatternSource := some "[0-9]+" }
    let patternModel : FlatModel := { fields := [patternTarget] }
    operationErrorOf (elaborateStringComputationOperation patternModel ["Form"]
      patternTarget.id (.literal "123")) =
        none := by
  native_decide

/- The exact model-prepared matcher accepts both literal and field-copy results without adding a second pattern evaluator. -/
example :
    patternTargetOutcomeOf (.literal "AAA") [] =
        some (.accepted { text := "AAA", nonempty := by decide }) ∧
      patternTargetOutcomeOf (.field (bare "PatternInput"))
        (stringCells patternInput.id "AAAA") =
          some (.accepted { text := "AAAA", nonempty := by decide }) := by
  native_decide

/- Pattern failure retains the attempted value, and the target's pattern check precedes its simultaneously failing minimum-length check. -/
example :
    patternTargetOutcomeOf (.literal "BBB") [] =
        some (.errored { text := "BBB", nonempty := by decide } .pattern) ∧
      patternTargetOutcomeOf (.field (bare "PatternInput"))
        (stringCells patternInput.id "B") =
          some (.errored { text := "B", nonempty := by decide } .pattern) := by
  native_decide

end A12Kernel.Conformance.StringComputationElaboration
