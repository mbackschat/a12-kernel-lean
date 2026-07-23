import A12Kernel.Elaboration.StarStringValueList
import A12Kernel.Elaboration.StringContext

/-! # Checked nested String-star literal value-list locks -/

namespace A12Kernel.Conformance.StarStringValueList

open A12Kernel

private def sku : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Sections", "Items"]
    name := "Sku"
    policy := { kind := .string }
    stringPolicy := { lineBreaksPermitted := true }
    repeatableScope := [10, 20] }

private def amount : FlatFieldDecl :=
  { sku with
    id := 8
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    stringPolicy := {} }

private def product : FlatFieldDecl :=
  { id := 1, groupPath := ["Shop"], name := "Product",
    policy := { kind := .string } }

private def quantity : FlatFieldDecl :=
  { product with
    id := 2
    name := "Quantity"
    policy := { kind := .number { scale := 0, signed := false } }
    stringPolicy := {} }

private def model : FlatModel :=
  { fields := [sku, amount, product, quantity]
    repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"], repeatability := some 2 },
      { level := 10, path := ["Shop", "Sections"], repeatability := some 2 }] }

private def customProduct : FlatFieldDecl :=
  { product with customType := some { name := "ProductCode" } }

private def customModel : FlatModel :=
  { model with fields := [sku, amount, customProduct, quantity] }

private def customSku : FlatFieldDecl :=
  { sku with
    stringPolicy := {}
    customType := some { name := "ProductCode" } }

private def customStarModel : FlatModel :=
  { model with fields := [customSku, amount, product, quantity] }

private def customRejection : RegisteredCustomRejection where
  projectCode := "PRODUCT_CODE_INVALID"

private def customValidator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "accepted" then none else some customRejection

private def customWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProductCode" then some customValidator else none

private def starPath (field : String := "Sku") : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Shop" }, { name := "Sections", starred := true },
      { name := "Items", starred := true }]
    field }

private def authored (quantifier : ValueListQuantifier)
    (values : List String := ["A"]) (field : String := "Sku")
    (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceStarStringValueListSource :=
  { quantifier, fields := starPath field, values, having }

private def fieldPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Shop"], field }

private def starValuesAuthored (quantifier : ValueListQuantifier)
    (field : String := "Product") (values : String := "Sku")
    (having : Option SurfaceCorrelatedHaving := none) :
    SurfaceStringValueListStarValuesSource :=
  { quantifier, field := fieldPath field, values := starPath values, having }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def sparseRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] }]

private def fullRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] },
  { group := 20, path := [1, 2] }, { group := 10, path := [2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def firstThen (first rest : RawCell) (environment : Env)
    (_ : FieldId) : RawCell :=
  if environment == [(10, 1), (20, 1)] then first else rest

private def unusedFilterRead (_ : Env) (_ : FieldId) : CheckedCell :=
  malformedCheckedCell

private def checkedStarReadFor (sourceModel : FlatModel)
    (read : Env → FieldId → RawCell) : Env → FieldId → CheckedCell :=
  fun environment id =>
    (sourceModel.checkContext { read := read environment }).read id

private def checkedStarRead
    (read : Env → FieldId → RawCell) : Env → FieldId → CheckedCell :=
  checkedStarReadFor model read

private def verdictOf (surface : SurfaceStarStringValueListSource)
    (rows : List RowAddr) (read : Env → FieldId → RawCell)
    (outer : Env := []) : Option Verdict :=
  match elaborateStarStringValueListSource model sku.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull (document rows) outer unusedFilterRead
          (checkedStarRead read) with
      | .error _ => none
      | .ok verdict => some verdict

private def partialResultOf (surface : SurfaceStarStringValueListSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Option PartialHavingValueListResult :=
  match elaborateStarStringValueListSource model sku.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartial (document rows) [] scope
          (checkedStarRead read) with
      | .error _ => none
      | .ok result => some result

private def partialVerdictOf (surface : SurfaceStarStringValueListSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Option Verdict :=
  match partialResultOf surface rows scope read with
  | some (.evaluated verdict) => some verdict
  | _ => none

private def directRaw (raw : RawCell) : RawFlatContext where
  read id := if id == product.id then raw else .empty

private def directRead (raw : RawCell) : FlatContext :=
  model.checkContext (directRaw raw)

private def starValuesVerdictOf (surface : SurfaceStringValueListStarValuesSource)
    (rows : List RowAddr) (direct : FlatContext)
    (read : Env → FieldId → RawCell) (outer : Env := []) : Option Verdict :=
  match elaborateStringValueListStarValuesSource model sku.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateFull (document rows) outer direct unusedFilterRead
          (checkedStarRead read) with
      | .error _ => none
      | .ok verdict => some verdict

private def partialStarValuesResultOf
    (surface : SurfaceStringValueListStarValuesSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (read : Env → FieldId → RawCell) :
    Option PartialHavingValueListResult :=
  match elaborateStringValueListStarValuesSource model sku.groupPath surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartial (document rows) [] scope direct
          (checkedStarRead read) with
      | .error _ => none
      | .ok result => some result

private def partialStarValuesVerdictOf
    (surface : SurfaceStringValueListStarValuesSource)
    (rows : List RowAddr) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (read : Env → FieldId → RawCell) : Option Verdict :=
  match partialStarValuesResultOf surface rows scope direct read with
  | some (.evaluated verdict) => some verdict
  | _ => none

private def customDirectContext (direct : String) : Option FlatContext := do
  let prepared ←
    (prepareFlatStringContext customWorld builtinStringPatternCompiler
      customModel).toOption
  pure (prepared.checkContext "en_US"
    (directRaw (.parsed (.str direct))))

private def customFieldsCell (direct : String) : Option (String ⊕ FormalCause) := do
  let context ← customDirectContext direct
  let checked ←
    (elaborateStringValueListStarValuesSource customModel sku.groupPath
      (starValuesAuthored .no)).toOption
  match (checked.resolvedFieldsSide context).cells with
  | [.present value] => some (.inl value)
  | [.unknown cause] => some (.inr cause)
  | _ => none

private def customStarValuesVerdictOf
    (quantifier : ValueListQuantifier) (direct : String)
    (read : Env → FieldId → RawCell) : Option Verdict := do
  let context ← customDirectContext direct
  let checked ←
    (elaborateStringValueListStarValuesSource customModel sku.groupPath
      (starValuesAuthored quantifier)).toOption
  (checked.evaluateFull (document fullRows) []
    context unusedFilterRead (checkedStarReadFor customModel read)).toOption

private def customCheckedStarRead
    (prepared :
      PreparedFlatStringContext customStarModel builtinStringPatternCompiler)
    (raw : Env → FieldId → RawCell) : Env → FieldId → CheckedCell :=
  fun environment id =>
    (prepared.checkContext "en_US" { read := raw environment }).read id

private def customFieldsStarVerdictOf
    (quantifier : ValueListQuantifier)
    (read : Env → FieldId → RawCell) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext customWorld builtinStringPatternCompiler
      customStarModel).toOption
  let checked ←
    (elaborateStarStringValueListSource customStarModel customSku.groupPath
      (authored quantifier ["accepted"])).toOption
  (checked.evaluateFull (document fullRows) [] unusedFilterRead
    (customCheckedStarRead prepared read)).toOption

private def customStarCell (value : String) : Option (String ⊕ FormalCause) := do
  let prepared ←
    (prepareFlatStringContext customWorld builtinStringPatternCompiler
      customStarModel).toOption
  let checked ←
    (elaborateStarStringValueListSource customStarModel customSku.groupPath
      (authored .no ["accepted"])).toOption
  let read := customCheckedStarRead prepared
    (firstThen (.parsed (.str value)) (.parsed (.str "other")))
  match checked.fields.valueListCell read [(10, 1), (20, 1)] with
  | .present token => some (.inl token)
  | .unknown cause => some (.inr cause)
  | .empty => none

private def customValuesStarVerdictOf
    (quantifier : ValueListQuantifier) (direct : RawCell)
    (read : Env → FieldId → RawCell) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext customWorld builtinStringPatternCompiler
      customStarModel).toOption
  let checked ←
    (elaborateStringValueListStarValuesSource customStarModel customSku.groupPath
      (starValuesAuthored quantifier)).toOption
  (checked.evaluateFull (document fullRows) []
    (prepared.checkContext "en_US" (directRaw direct)) unusedFilterRead
    (customCheckedStarRead prepared read)).toOption

private def starValuesErrorOf (surface : SurfaceStringValueListStarValuesSource) :
    Option StarStringValueListElabError :=
  match elaborateStringValueListStarValuesSource model sku.groupPath surface with
  | .ok _ => none
  | .error error => some error

private def errorOf (surface : SurfaceStarStringValueListSource) :
    Option StarStringValueListElabError :=
  match elaborateStarStringValueListSource model sku.groupPath surface with
  | .ok _ => none
  | .error error => some error

private def repetition (origin : HavingOrigin) (groups : List String) :
    SurfaceHavingRepetitionRef :=
  { origin, group := .path { base := .absolute, groups } }

private def earlierSibling : SurfaceCorrelatedHaving :=
  .and
    (.compareRepetitions .equal
      (repetition .inner ["Shop", "Sections"])
      (repetition .outer ["Shop", "Sections"]))
    (.compareRepetitions .less
      (repetition .inner ["Shop", "Sections", "Items"])
      (repetition .outer ["Shop", "Sections", "Items"]))

private def selectedStringOnly (environment : Env) (_ : FieldId) : RawCell :=
  if environment == [(10, 1), (20, 1)] then .parsed (.str "A")
  else .rejected .malformed

/- Starred String cells reuse evaluated-cache CRLF normalization before literal membership. -/
example :
    verdictOf (authored .atLeastOne ["A\nB"]) fullRows
      (firstThen (.parsed (.str "A\r\nB")) .empty) =
        some (.fired .value) := by
  native_decide

/- Partial validation skips a rule containing `Having` before malformed topology or either String reader. -/
example :
    partialResultOf (authored .atLeastOne (having := some earlierSibling))
        [{ group := 20, path := [1, 1] }] .full selectedStringOnly =
      some .skippedHaving ∧
    partialStarValuesResultOf
        (starValuesAuthored .atLeastOne (having := some earlierSibling))
        [{ group := 20, path := [1, 1] }] .full
        (directRead (.rejected .malformed)) selectedStringOnly =
      some .skippedHaving := by
  native_decide

/- A checked `Having` filters before String classification and escalates a firing on either quantifier side. -/
example :
    verdictOf (authored .atLeastOne (having := some earlierSibling)) fullRows
        selectedStringOnly [(10, 1), (20, 2)] = some (.fired .omission) ∧
    starValuesVerdictOf
        (starValuesAuthored .atLeastOne (having := some earlierSibling)) fullRows
        (directRead (.parsed (.str "A"))) selectedStringOnly
        [(10, 1), (20, 2)] =
      some (.fired .omission) := by
  native_decide

/- A direct String subject consumes the expanded starred member set through the same three quantifiers. -/
example :
    starValuesVerdictOf (starValuesAuthored .atLeastOne) fullRows
        (directRead (.parsed (.str "A")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some (.fired .value) ∧
    starValuesVerdictOf (starValuesAuthored .no) fullRows
        (directRead (.parsed (.str "C")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some (.fired .value) ∧
    starValuesVerdictOf (starValuesAuthored .notAll) fullRows
        (directRead (.parsed (.str "C")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some (.fired .value) := by
  native_decide

/- A caller-prepared direct custom String remains distinguishable from its registered rejection instead of being resampled through the ordinary fail-closed checker. -/
example :
    customFieldsCell "accepted" = some (.inl "accepted") ∧
    customFieldsCell "rejected" =
      some (.inr (.registeredCustomValidation customRejection)) ∧
    customStarValuesVerdictOf .no "accepted"
        (firstThen (.parsed (.str "accepted")) (.parsed (.str "other"))) =
      some .notFired ∧
    customStarValuesVerdictOf .no "rejected"
        (firstThen (.parsed (.str "accepted")) (.parsed (.str "other"))) =
      some .unknown := by
  native_decide

/- Both String-star directions consume the same caller-prepared checked rows; accepted custom tokens remain values and exact rejections remain unavailable. -/
example :
    customStarCell "accepted" = some (.inl "accepted") ∧
    customStarCell "rejected" =
      some (.inr (.registeredCustomValidation customRejection)) ∧
    customFieldsStarVerdictOf .atLeastOne
        (firstThen (.parsed (.str "accepted")) (.parsed (.str "other"))) =
      some (.fired .value) ∧
    customFieldsStarVerdictOf .no
        (firstThen (.parsed (.str "rejected")) (.parsed (.str "accepted"))) =
      some .unknown ∧
    customValuesStarVerdictOf .atLeastOne (.parsed (.str "accepted"))
        (firstThen (.parsed (.str "accepted")) (.parsed (.str "other"))) =
      some (.fired .value) ∧
    customValuesStarVerdictOf .notAll (.parsed (.str "accepted"))
        (firstThen (.parsed (.str "rejected")) (.parsed (.str "accepted"))) =
      some .unknown := by
  native_decide

/- Empty and malformed starred members retain values-side omission and poison rather than becoming literal tokens. -/
example :
    starValuesVerdictOf (starValuesAuthored .atLeastOne) fullRows
        (directRead (.parsed (.str "A")))
        (firstThen .empty (.parsed (.str "A"))) =
      some (.fired .value) ∧
    starValuesVerdictOf (starValuesAuthored .no) sparseRows
        (directRead (.parsed (.str "C"))) (firstThen .empty .empty) =
      some (.fired .omission) ∧
    starValuesVerdictOf (starValuesAuthored .notAll) fullRows
        (directRead (.parsed (.str "C")))
        (firstThen (.rejected .malformed) (.parsed (.str "A"))) =
      some .unknown := by
  native_decide

/- A malformed fields cell is skipped by `AtLeastOne` and `NotAll`, but poisons `No`. -/
example :
    verdictOf (authored .atLeastOne) fullRows
        (firstThen (.rejected .malformed) (.parsed (.str "A"))) =
      some (.fired .value) ∧
    verdictOf (authored .no) fullRows
        (firstThen (.rejected .malformed) (.parsed (.str "B"))) =
      some .unknown ∧
    verdictOf (authored .notAll) fullRows
        (firstThen (.rejected .malformed) (.parsed (.str "A"))) =
      some .notFired := by
  native_decide

/- Hierarchical omitted tails affect fired `No`, but not fired `NotAll`. -/
example :
    verdictOf (authored .no) sparseRows
        (firstThen (.parsed (.str "B")) .empty) = some (.fired .omission) ∧
    verdictOf (authored .no) fullRows
        (firstThen (.parsed (.str "B")) (.parsed (.str "B"))) =
      some (.fired .value) ∧
    verdictOf (authored .notAll) sparseRows
        (firstThen (.parsed (.str "B")) .empty) = some (.fired .value) := by
  native_decide

private def entity (path : List String) (indices : List RelevanceIndex) :
    RelevantEntityPattern :=
  { path, indices }

private def firstSkuOnly : ValidationRelevanceScope :=
  .partialSet [
    entity sku.path [.concrete 1, .concrete 1, .concrete 1, .concrete 1]]

private def allConcreteSkus : ValidationRelevanceScope :=
  .partialSet [
    entity sku.path [.concrete 1, .concrete 1, .concrete 1, .concrete 1],
    entity sku.path [.concrete 1, .concrete 1, .concrete 2, .concrete 1],
    entity sku.path [.concrete 1, .concrete 2, .concrete 1, .concrete 1],
    entity sku.path [.concrete 1, .concrete 2, .concrete 2, .concrete 1]]

private def allConcreteSkusAndProduct : ValidationRelevanceScope :=
  match allConcreteSkus with
  | .full => .full
  | .partialSet entities =>
      .partialSet (entity product.path [.concrete 1, .concrete 1] :: entities)

private def wildcardSkusAndProduct : ValidationRelevanceScope :=
  .partialSet [
    entity product.path [.concrete 1, .concrete 1],
    entity sku.path [.concrete 1, .all, .all, .concrete 1]]

/- Partial validation reads only relevant cells: their witness survives for the existential operators, while `No` retains relevance poison. -/
example :
    partialVerdictOf (authored .atLeastOne) fullRows firstSkuOnly
        (firstThen (.parsed (.str "A")) (.rejected .malformed)) =
      some (.fired .value) ∧
    partialVerdictOf (authored .notAll) fullRows firstSkuOnly
        (firstThen (.parsed (.str "B")) (.rejected .malformed)) =
      some (.fired .value) ∧
    partialVerdictOf (authored .no) fullRows firstSkuOnly
        (firstThen (.parsed (.str "B")) (.rejected .malformed)) =
      some .unknown := by
  native_decide

/- A values-side star needs wildcard extent for `No` and `NotAll`; `AtLeastOne` may still use concrete relevant members. -/
example :
    partialStarValuesVerdictOf (starValuesAuthored .atLeastOne) fullRows
        allConcreteSkusAndProduct (directRead (.parsed (.str "A")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some (.fired .value) ∧
    partialStarValuesVerdictOf (starValuesAuthored .no) fullRows
        allConcreteSkusAndProduct (directRead (.parsed (.str "C")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some .unknown ∧
    partialStarValuesVerdictOf (starValuesAuthored .notAll) fullRows
        allConcreteSkusAndProduct (directRead (.parsed (.str "C")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some .unknown ∧
    partialStarValuesVerdictOf (starValuesAuthored .notAll) fullRows
        wildcardSkusAndProduct (directRead (.parsed (.str "C")))
        (firstThen (.parsed (.str "A")) (.parsed (.str "B"))) =
      some (.fired .value) := by
  native_decide

/- Listing every current row concretely does not establish the extent of a star: `No` remains UNKNOWN, while the existential operators may use the individually relevant cells. -/
example :
    partialVerdictOf (authored .atLeastOne) fullRows allConcreteSkus
        (firstThen (.parsed (.str "A")) (.parsed (.str "A"))) =
      some (.fired .value) ∧
    partialVerdictOf (authored .notAll) fullRows allConcreteSkus
        (firstThen (.parsed (.str "B")) (.parsed (.str "B"))) =
      some (.fired .value) ∧
    partialVerdictOf (authored .no) fullRows allConcreteSkus
        (firstThen (.parsed (.str "B")) (.parsed (.str "B"))) =
      some .unknown := by
  native_decide

/- Both sides retain their own exact String kind gate. -/
example :
    starValuesErrorOf (starValuesAuthored .atLeastOne "Quantity") =
      some (.fieldNotString quantity.path .number) := by
  native_decide

/- Static admission keeps the literal side nonempty and the starred field exactly String-valued. -/
example :
    errorOf (authored .atLeastOne []) = some .emptyValues ∧
    errorOf (authored .atLeastOne ["1"] "Amount") =
      some (.fieldNotString amount.path .number) := by
  native_decide

end A12Kernel.Conformance.StarStringValueList
