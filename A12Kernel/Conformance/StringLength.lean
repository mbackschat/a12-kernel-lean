import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Direct String and Length conformance locks -/

namespace A12Kernel.Conformance.StringLength

open A12Kernel

private def stringField : FlatStringField := { id := 6 }

private def checked (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (raw : RawCell) : FlatContext where
  read _ := checked raw

private def noncanonicalPresentEmptyContext : FlatContext where
  read _ := { rawPresent := true, parsed := some (.str ""), findings := [] }

private def directEqualsAbc : FlatCondition :=
  .compare (.string .equal stringField "ABC")

private def directEqualsEmpty : FlatCondition :=
  .compare (.string .equal stringField "")

private def directNotEqualsAbc : FlatCondition :=
  .compare (.string .notEqual stringField "ABC")

private def directNotEqualsEmpty : FlatCondition :=
  .compare (.string .notEqual stringField "")

private def lengthLessThanFive : FlatCondition :=
  .compare (.stringLength .less stringField 5)

private def lengthGreaterOrEqualZero : FlatCondition :=
  .compare (.stringLength .greaterEqual stringField 0)

private def lengthLessOrEqualZero : FlatCondition :=
  .compare (.stringLength .lessEqual stringField 0)

private def lengthGreaterThanMinusOne : FlatCondition :=
  .compare (.stringLength .greater stringField (-1))

example : directEqualsAbc.evalFull (context .empty) true = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context .empty) true = .fired .omission := by
  native_decide

example : lengthGreaterOrEqualZero.evalFull (context .empty) true = .fired .value := by
  native_decide

/- Empty Length can grow: a true upper bound is omission-typed, while a true lower bound is value-typed. -/
example :
    lengthLessOrEqualZero.evalFull (context .empty) true = .fired .omission ∧
      lengthGreaterThanMinusOne.evalFull (context .empty) true = .fired .value := by
  native_decide

example : directEqualsAbc.evalFull (context (.parsed (.str ""))) true = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.str ""))) true = .fired .omission := by
  native_decide

example : lengthLessThanFive.evalFull noncanonicalPresentEmptyContext true = .fired .omission := by
  native_decide

example : directEqualsAbc.evalFull (context .empty) false = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context .empty) false = .notFired := by
  decide

example : lengthGreaterOrEqualZero.evalFull (context .empty) false = .notFired := by
  decide

example : directEqualsAbc.evalFull (context (.parsed (.str "ABC"))) true = .fired .value := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.str "ABC"))) true = .fired .value := by
  native_decide

example : lengthGreaterOrEqualZero.evalFull (context (.parsed (.str "ABC"))) true =
    .fired .value := by
  native_decide

example : directEqualsAbc.evalFull (context (.parsed (.str "ABCDEF"))) true = .notFired := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.str "ABCDEF"))) true = .notFired := by
  native_decide

example : lengthGreaterOrEqualZero.evalFull (context (.parsed (.str "ABCDEF"))) true =
    .fired .value := by
  native_decide

example : directEqualsEmpty.evalFull (context (.parsed (.str "ABC"))) true = .notFired := by
  decide

example : directNotEqualsAbc.evalFull (context .empty) true = .notFired := by
  decide

example : directNotEqualsAbc.evalFull (context (.parsed (.str "ABC"))) true = .notFired := by
  decide

example : directNotEqualsAbc.evalFull (context (.parsed (.str "XYZ"))) true =
    .fired .value := by
  decide

example : directNotEqualsEmpty.evalFull (context (.parsed (.str "ABC"))) true =
    .notFired := by
  decide

example : directNotEqualsEmpty.evalFull (context (.rejected .malformed)) true =
    .unknown := by
  decide

example : directEqualsEmpty.evalFull (context (.rejected .malformed)) true = .unknown := by
  decide

example : directEqualsEmpty.evalFull (context (.parsed (.num 1))) true = .unknown := by
  decide

example : directEqualsAbc.evalFull (context (.rejected .malformed)) true = .unknown := by
  decide

example : lengthLessThanFive.evalFull (context (.rejected .malformed)) true = .unknown := by
  decide

example : directEqualsAbc.evalFull (context (.parsed (.num 1))) true = .unknown := by
  decide

example : lengthLessThanFive.evalFull (context (.parsed (.num 1))) true = .unknown := by
  decide

/- Field kind alone does not determine empty behavior: the same observation is suppressed by direct equality and fires through Length. -/
example : directEqualsAbc.evalFull (context .empty) true !=
    lengthLessThanFive.evalFull (context .empty) true := by
  native_decide

/- A substituted empty result is not uniformly omission-typed: direction makes `Length >= 0` a value firing. -/
example : lengthLessThanFive.evalFull (context .empty) true !=
    lengthGreaterOrEqualZero.evalFull (context .empty) true := by
  native_decide

example : utf16CodeUnitLength "é" = 2 := by
  native_decide

example : utf16CodeUnitLength "😀" = 2 := by
  native_decide

private def productCodePath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := "ProductCode" }

private def productCodeDecl : FlatFieldDecl :=
  { id := stringField.id, groupPath := ["Order"], name := "ProductCode",
    policy := { kind := .string } }

private def productCodeModel : FlatModel :=
  { fields := [productCodeDecl] }

private def quantityDecl : FlatFieldDecl :=
  { id := 7, groupPath := ["Order"], name := "Quantity",
    policy := { kind := .number { scale := 0, signed := false } } }

private def numberModel : FlatModel :=
  { fields := [quantityDecl] }

private def quantityPath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := "Quantity" }

private def elaborationError? : Except ElabError α → Option ElabError
  | .ok _ => none
  | .error error => some error

example : (elaborate productCodeModel ["Order"]
    (.compare .equal productCodePath (.string "ABC"))).isOk = true := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.lengthCompare .less productCodePath 5)).isOk = true := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.lengthCompare .greaterEqual productCodePath 0)).isOk = true := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.compare .notEqual productCodePath (.string "ABC"))).isOk = true := by
  native_decide

example :
    (elaborate productCodeModel ["Order"]
      (.lengthCompare .lessEqual productCodePath 3)).isOk = true ∧
      (elaborate productCodeModel ["Order"]
        (.lengthCompare .greater productCodePath 2)).isOk = true := by
  native_decide

/- Equality remains outside the scale-erasing flat surface; both exact operators need the authored literal scale. -/
example :
    elaborationError? (elaborate productCodeModel ["Order"]
        (.lengthCompare .equal productCodePath 3)) =
        some (.unsupportedOperator .equal) ∧
      elaborationError? (elaborate productCodeModel ["Order"]
        (.lengthCompare .notEqual productCodePath 3)) =
        some (.unsupportedOperator .notEqual) := by
  native_decide

example : elaborationError? (elaborate numberModel ["Order"]
    (.lengthCompare .less quantityPath 5)) =
    some (.lengthOperandKindMismatch ["Order", "Quantity"] .number) := by
  native_decide

example : (elaborate productCodeModel ["Order"]
    (.fieldNotFilled productCodePath)).isOk = true := by
  native_decide

private def scaleTwoTargetDecl : FlatFieldDecl :=
  { id := 8, groupPath := ["Order"], name := "ScaleTwoTarget",
    policy := { kind := .number { scale := 2, signed := false } } }

private def checkedLengthModel : FlatModel :=
  { fields := [productCodeDecl, quantityDecl, scaleTwoTargetDecl] }

private def digitCodeDecl : FlatFieldDecl :=
  {
    id := 10
    groupPath := ["Order"]
    name := "DigitCode"
    policy := { kind := .string }
    stringPatternSource := some asciiDigitsPatternSource
  }

private def customCodeDecl : FlatFieldDecl :=
  {
    id := 11
    groupPath := ["Order"]
    name := "CustomCode"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" }
  }

private def preparedLengthModel : FlatModel :=
  { fields := [digitCodeDecl, customCodeDecl] }

private def customLengthRejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def customLengthValidator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "accepted" then none else some customLengthRejection

private def preparedLengthWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some customLengthValidator else none

private def preparedLengthPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def preparedLengthRaw (field : FieldId) (source : String) :
    RawFlatContext where
  read id := if id == field then .parsed (.str source) else .empty

private def preparedLengthVerdict (name : String) (field : FieldId)
    (source : String) (expected : Rat) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext preparedLengthWorld builtinStringPatternCompiler
      preparedLengthModel).toOption
  (elaborateAndEvalNumericComparison prepared "en_US" ["Order"]
    (preparedLengthRaw field source) true {
      op := .ordinary .equal
      left := .atom (.stringLength (preparedLengthPath name))
      right := .literal { value := expected, authoredScale := 0 }
    }).toOption

private def checkedLengthAtom : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.stringLength productCodePath)

private def checkedLengthLiteral (value : Rat) (authoredScale : Int := 0) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale }

private def checkedLengthComparison (op : NumericComparisonOp) (value : Rat)
    (authoredScale : Int := 0) : SurfaceNumericComparison :=
  { op := .ordinary op
    left := checkedLengthAtom
    right := checkedLengthLiteral value authoredScale }

private def checkedLengthRaw (source : RawCell) (target : RawCell := .empty) :
    RawFlatContext where
  read field :=
    if field == stringField.id then source
    else if field == quantityDecl.id then target
    else .empty

private def checkedLengthVerdict (surface : SurfaceNumericComparison)
    (source : RawCell) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext preparedLengthWorld builtinStringPatternCompiler
      checkedLengthModel).toOption
  (elaborateAndEvalNumericComparison prepared "en_US" ["Order"]
    (checkedLengthRaw source) true surface).toOption

private def checkedLengthError (surface : SurfaceNumericComparison) :
    Option NumericValidationElabError :=
  match elaborateNumericComparison checkedLengthModel ["Order"] surface with
  | .ok _ => none
  | .error error => some error

/- `Length` is a fixed scale-0 numeric source: exact operators retain the authored literal scale instead of using the scale-erasing flat projection. -/
example :
    (elaborateNumericComparison checkedLengthModel ["Order"]
      (checkedLengthComparison .equal 3)).isOk = true ∧
    (elaborateNumericComparison checkedLengthModel ["Order"]
      (checkedLengthComparison .notEqual 3)).isOk = true ∧
    checkedLengthError (checkedLengthComparison .equal 3 2) =
      some (.exactScaleMismatch
        (NumericScaleSummary.field 0) (NumericScaleSummary.constant 2)) ∧
    (elaborateNumericComparison checkedLengthModel ["Order"]
      { (checkedLengthComparison .equal 3 2) with
        suppressExactScaleWarning := true }).isOk = true := by
  native_decide

/- Standalone numeric evaluation consumes both legal prepared String profiles before measuring Length. -/
example :
    preparedLengthVerdict "DigitCode" digitCodeDecl.id "123" 3 =
        some (.fired .value) ∧
      preparedLengthVerdict "DigitCode" digitCodeDecl.id "12A" 3 =
        some .unknown ∧
      preparedLengthVerdict "CustomCode" customCodeDecl.id "accepted" 8 =
        some (.fired .value) ∧
      preparedLengthVerdict "CustomCode" customCodeDecl.id "rejected" 8 =
        some .unknown := by
  native_decide

/- The common numeric evaluator preserves UTF-16 measurement, grow-only empty zero, formal unavailability, arithmetic, and wrapper composition. -/
example :
    checkedLengthVerdict (checkedLengthComparison .equal 2)
        (.parsed (.str "é")) = some (.fired .value) ∧
    checkedLengthVerdict (checkedLengthComparison .equal 0) .empty =
      some (.fired .omission) ∧
    checkedLengthVerdict (checkedLengthComparison .equal 0)
        (.rejected .malformed) = some .unknown ∧
    checkedLengthVerdict {
        op := .ordinary .equal
        left := .binary .add checkedLengthAtom (checkedLengthLiteral 1)
        right := checkedLengthLiteral 4 }
        (.parsed (.str "ABC")) = some (.fired .value) ∧
    checkedLengthVerdict {
        op := .ordinary .equal
        left := .abs checkedLengthAtom
        right := checkedLengthLiteral 3 }
        (.parsed (.str "ABC")) = some (.fired .value) := by
  native_decide

/- Static admission rejects a wrong-kind source through the Length-specific boundary. -/
example :
    checkedLengthError {
      op := .ordinary .less
      left := .atom (.stringLength quantityPath)
      right := checkedLengthLiteral 5 } =
        some (.lengthOperandNotEvaluatedString ["Order", "Quantity"]) := by
  native_decide

private def rawLengthDecl : FlatFieldDecl :=
  { id := 9
    groupPath := ["Order"]
    name := "RawText"
    policy := { kind := .string }
    stringValueMode := .raw
    stringPolicy := { lineBreaksPermitted := true } }

private def rawLengthPath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := "RawText" }

private def rawLengthModel : FlatModel :=
  { fields := [rawLengthDecl, quantityDecl] }

/- A raw String remains presence-only except for its strict whole-rule metadata form; the general numeric source cannot read it. -/
example :
    (match elaborateNumericComparison rawLengthModel ["Order"] {
        op := .ordinary .less
        left := .atom (.stringLength rawLengthPath)
        right := checkedLengthLiteral 5 } with
      | .ok _ => none
      | .error error => some error) =
        some (.lengthOperandNotEvaluatedString ["Order", "RawText"]) := by
  native_decide

private def checkedLengthComputationContextFromCells
    (source target : CheckedCell) :
    ScalarComputationContext where
  read field :=
    if field == stringField.id then source
    else if field == quantityDecl.id then target
    else formalCheck { kind := .number { scale := 0, signed := false } } .empty

private def checkedLengthComputationContext
    (source : RawCell) (target : RawCell := .empty) :
    ScalarComputationContext :=
  checkedLengthComputationContextFromCells
    (productCodeDecl.checkRaw source) (quantityDecl.checkRaw target)

private def checkedLengthComputationResult
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (source : RawCell) : Option NumericComputationResult :=
  match elaborateNumericComputationOperation checkedLengthModel ["Order"]
      quantityDecl.id expression with
  | .error _ => none
  | .ok operation =>
      operation.evaluate (checkedLengthComputationContext source) |>.toOption

private def checkedLengthComputationResultFromCell
    (source : CheckedCell) : Option NumericComputationResult :=
  match elaborateNumericComputationOperation checkedLengthModel ["Order"]
      quantityDecl.id checkedLengthAtom with
  | .error _ => none
  | .ok operation =>
      operation.evaluate (checkedLengthComputationContextFromCells source
        (quantityDecl.checkRaw .empty)) |>.toOption

private def checkedLengthComputationError
    (sourceModel : FlatModel) (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation sourceModel ["Order"] target expression with
  | .ok _ => none
  | .error error => some error

/- Computation consumes the same checked String cache, maps clean empty to numeric zero, preserves poison, and composes through arithmetic. -/
example :
    checkedLengthComputationResult checkedLengthAtom .empty =
      some (.value 0) ∧
    checkedLengthComputationResult checkedLengthAtom
        (.parsed (.str "é")) = some (.value 2) ∧
    checkedLengthComputationResult checkedLengthAtom
        (.rejected .declaredConstraint) =
      some (.poison .declaredConstraint) ∧
    checkedLengthComputationResultFromCell
        ((productCodeDecl.checkRaw .empty).withFinding .required) =
      some (.value 0) ∧
    checkedLengthComputationResult
        (.binary .add checkedLengthAtom (checkedLengthLiteral 1))
        (.parsed (.str "ABC")) = some (.value 4) := by
  native_decide

/- Result-scale checking, raw-String admission, and field-reference traversal apply to the new atom in computation too. -/
example :
    checkedLengthComputationError checkedLengthModel scaleTwoTargetDecl.id
        checkedLengthAtom =
      some (.operationScaleMismatch 2 (NumericScaleSummary.field 0)) ∧
    checkedLengthComputationError rawLengthModel quantityDecl.id
        (.atom (.stringLength rawLengthPath)) =
      some (.lengthOperandNotEvaluatedString ["Order", "RawText"]) ∧
    (match elaborateNumericComputationOperation checkedLengthModel ["Order"]
        quantityDecl.id checkedLengthAtom with
      | .ok operation =>
          operation.core.expression.anyAtom
            (CheckedNumericComputationAtom.references
              checkedLengthModel stringField.id)
      | .error _ => false) = true := by
  native_decide

private def generatedLengthVerdict (source : RawCell) (target : Rat) :
    Option Verdict := do
  let operation ← (elaborateNumericComputationOperation checkedLengthModel ["Order"]
    quantityDecl.id checkedLengthAtom).toOption
  let comparison ← (operation.generatedMismatchComparison none).toOption
  pure (comparison.evalFull
    (checkedLengthModel.checkContext
      (checkedLengthRaw source (.parsed (.num target)))) true)

/- Generated validation narrows the already-checked computation atom without reconstructing or re-elaborating surface syntax. -/
example :
    generatedLengthVerdict (.parsed (.str "ABC")) 3 =
      some .notFired ∧
    generatedLengthVerdict (.parsed (.str "ABC")) 4 =
      some (.fired .value) := by
  native_decide

end A12Kernel.Conformance.StringLength
