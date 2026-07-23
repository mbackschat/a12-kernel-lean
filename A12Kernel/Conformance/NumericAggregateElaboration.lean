import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.NumericComputation

/-! # Checked Number-list and finite-star lowering locks -/

namespace A12Kernel.Conformance.NumericAggregateElaboration

open A12Kernel

private def unsignedA : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "UnsignedA",
    policy := { kind := .number { scale := 0, signed := false } } }

private def signedB : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "SignedB",
    policy := { kind := .number { scale := 0, signed := true } } }

private def unsignedC : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "UnsignedC",
    policy := { kind := .number { scale := 0, signed := false } } }

private def text : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Text",
    policy := { kind := .string } }

private def repeated : FlatFieldDecl :=
  { id := 4, groupPath := ["Form", "Rows"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

private def repeatedPrice : FlatFieldDecl :=
  { id := 5, groupPath := ["Form", "Rows"], name := "Price",
    policy := { kind := .number { scale := 2, signed := true } },
    repeatableScope := [10] }

private def repeatedText : FlatFieldDecl :=
  { id := 6, groupPath := ["Form", "Rows"], name := "Label",
    policy := { kind := .string }, repeatableScope := [10] }

private def otherRepeated : FlatFieldDecl :=
  { id := 7, groupPath := ["Form", "Other"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [20] }

private def nestedRepeated : FlatFieldDecl :=
  { id := 8, groupPath := ["Form", "Rows", "Details"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10, 30] }

private def filterLeft : FlatFieldDecl :=
  { id := 9, groupPath := ["Form", "Rows"], name := "FilterLeft",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

private def filterRight : FlatFieldDecl :=
  { id := 10, groupPath := ["Form", "Rows"], name := "FilterRight",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [10] }

private def rows : RepeatableGroupDecl :=
  { level := 10, path := ["Form", "Rows"], repeatability := some 3 }

private def otherRows : RepeatableGroupDecl :=
  { level := 20, path := ["Form", "Other"], repeatability := some 3 }

private def detailRows : RepeatableGroupDecl :=
  { level := 30, path := ["Form", "Rows", "Details"], repeatability := some 2 }

private def model : FlatModel :=
  { fields := [unsignedA, signedB, unsignedC, text, repeated, filterLeft,
      filterRight]
    repeatableGroups := [rows] }

private def productModel : FlatModel :=
  { fields := model.fields ++ [repeatedPrice, repeatedText, otherRepeated,
      nestedRepeated]
    repeatableGroups := [rows, otherRows, detailRows] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def absolute (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def sum (first : SurfaceFieldPath)
    (rest : List SurfaceFieldPath) : SurfaceNumericAggregateFields :=
  { first, rest }

private def raw (a b c : RawCell) : RawFlatContext where
  read field :=
    if field = unsignedA.id then a
    else if field = signedB.id then b
    else if field = unsignedC.id then c
    else .empty

private def operandOf (authored : SurfaceNumericAggregateFields)
    (input : RawFlatContext) : Option NumericOperand :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .error _ => none
  | .ok checked => some (checked.evaluateSum input)

private def extremumOperandOf (op : NumericExtremumOp)
    (authored : SurfaceNumericAggregateFields) (input : RawFlatContext) : Option NumericOperand :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .error _ => none
  | .ok checked => some (checked.evaluateExtremum op input)

private def errorOf (authored : SurfaceNumericAggregateFields) : Option NumericAggregateElabError :=
  match elaborateNumericAggregateFields model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def tenPow50 : Rat := 10 ^ 50

private def starredAmount : SurfaceSingleStarFieldPath :=
  { base := .absolute
    groupsBeforeStar := ["Form"]
    starredGroup := "Rows"
    field := "Amount" }

private def repeatedRaw (candidates : List RowIndex) (a b c : RawCell) :
    RawSingleGroupContext where
  candidates := candidates
  read row field :=
    if field != repeated.id then .empty
    else match row with
      | 1 => a
      | 2 => b
      | 3 => c
      | _ => .empty

private def starElabErrorOf (source : SurfaceSingleStarFieldPath)
    (targetModel : FlatModel := model) : Option NumericStarElabError :=
  match elaborateNumericStarSource targetModel ["Form"] source with
  | .ok _ => none
  | .error error => some error

private def starSumOf (raw : RawSingleGroupContext) : Option NumericOperand :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateSum raw with
      | .ok operand => some operand
      | .error _ => none

private def starExtremumOf (op : NumericExtremumOp) (raw : RawSingleGroupContext) :
    Option NumericOperand :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateExtremum op raw with
      | .ok operand => some operand
      | .error _ => none

private def starContextErrorOf (raw : RawSingleGroupContext) :
    Option NumericStarContextError :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateSum raw with
      | .ok _ => none
      | .error error => some error

private def starFirstFilledOf (raw : RawSingleGroupContext) :
    Option FirstFilledNumberResult :=
  match elaborateNumericStarSource model ["Form"] starredAmount with
  | .error _ => none
  | .ok checked => match checked.evaluateFirstFilled raw with
      | .ok result => some result
      | .error _ => none

private def aggregateStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := true }]
    field := "Amount" }

private def productStar (field : String) (group : String := "Rows") :
    SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := group, starred := true }]
    field }

private def nestedProductStar (outerStar : Bool) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := outerStar },
      { name := "Details", starred := true }]
    field := "Amount" }

private def productSource (left right : SurfaceStarFieldPath) :
    SurfaceNumericProductAggregate :=
  { left, right }

private def productErrorOf (left right : SurfaceStarFieldPath) :
    Option NumericProductAggregateElabError :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource left right) with
  | .ok _ => none
  | .error error => some error

private def productRead (left right : RowIndex → RawCell)
    (environment : Env) (field : FieldId) : RawCell :=
  match environment with
  | [(10, row)] =>
      if field == repeated.id then left row
      else if field == repeatedPrice.id then right row
      else .empty
  | _ => .empty

private def productDocument (selectedRows : List RowIndex) : Document :=
  { instantiatedRows := selectedRows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

private def productValidationOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) : Option NumericOperand :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluateValidation (productDocument selectedRows) []
        (productRead left right)).toOption

private def productCheckedRead (left right : RowIndex → RawCell)
    (requiredLeft : Bool) (environment : Env) (field : FieldId) : CheckedCell :=
  let raw := productRead left right environment field
  if field == repeated.id then
    let cell := repeated.checkRaw raw
    if requiredLeft && raw == .presentEmpty then
      { cell with findings := [.required] }
    else
      cell
  else if field == repeatedPrice.id then
    repeatedPrice.checkRaw raw
  else
    malformedCheckedCell

private def productCheckedValidationOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) (requiredLeft : Bool := false) :
    Option NumericOperand :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluateAt .validation (productDocument selectedRows) []
        (productCheckedRead left right requiredLeft)).toOption

private def productComputationOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) (requiredLeft : Bool := false) :
    Option NumericComputationResult :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluateComputation (productDocument selectedRows) []
        (productCheckedRead left right requiredLeft)).toOption

private def productPartialOf (selectedRows : List RowIndex)
    (left right : RowIndex → RawCell) (scope : ValidationRelevanceScope) :
    Option PartialValidationNumberAggregateResult :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked =>
      (checked.evaluatePartial (productDocument selectedRows) [] scope
        (productRead left right)).toOption

private def productScale : Option NumericScaleSummary :=
  match elaborateNumericProductAggregate productModel ["Form"]
      (productSource (productStar "Amount") (productStar "Price")) with
  | .error _ => none
  | .ok checked => some checked.scaleSummary

private def cells3 (first second third : RawCell) : RowIndex → RawCell
  | 1 => first
  | 2 => second
  | 3 => third
  | _ => .empty

private def productRelevance (path : List String)
    (indices : List RelevanceIndex) : RelevantEntityPattern :=
  { path, indices }

/- The dedicated pair admits exactly two same-group Number stars, permits the same wildcarded field twice as the A12 checker does, and rejects a different group or wrong kind. -/
example :
    productErrorOf aggregateStar aggregateStar = none ∧
      productErrorOf (productStar "Amount") (productStar "Price") = none ∧
      productErrorOf (productStar "Amount") (productStar "Amount" "Other") =
        some (.differentGroups ["Form", "Rows"] ["Form", "Other"]) ∧
      productErrorOf (productStar "Amount") (productStar "Label") =
        some (.source (.fieldNotNumber repeatedText.path)) := by
  native_decide

/- Only the lowest repeatable level may be starred. A named outer row plus an inner star remains legal. -/
example :
    productErrorOf (nestedProductStar true) (nestedProductStar true) =
        some (.wildcardNotLowest nestedRepeated.path) ∧
      productErrorOf (nestedProductStar false) (nestedProductStar false) = none := by
  native_decide

/- Both fields are read from each shared canonical environment: 2·3 + 4·5 is 26, not a cross-paired 22. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num 2)) (.parsed (.num 4)) (.parsed (.num 0)))
      (cells3 (.parsed (.num 3)) (.parsed (.num 5)) (.parsed (.num 0))) =
        some (.value 26 .fixed) := by
  native_decide

/- Multiplication and addition are staged at precision 50 in canonical row order. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num tenPow50)) (.parsed (.num (-tenPow50)))
        (.parsed (.num (3 / 5))))
      (cells3 (.parsed (.num 1)) (.parsed (.num 1)) (.parsed (.num 1))) =
        some (.value (3 / 5) .fixed) := by
  native_decide

/- Each row product is rounded before entering the running sum; exact rational multiplication would retain the final `3 / 5`. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num (tenPow50 - 1))) (.parsed (.num 0))
        (.parsed (.num 0)))
      (cells3 (.parsed (.num (3 / 5))) (.parsed (.num 0))
        (.parsed (.num 0))) =
        some (.value (tenPow50 * 3 / 5 - 1) .fixed) := by
  native_decide

/- Empty cells substitute zero but retain declaration-owned arithmetic directions; any omitted declared row makes the successful fold both-directionally fillable. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num 2)) (.parsed (.num 10)) (.parsed (.num 0)))
      (cells3 (.parsed (.num 3)) .presentEmpty (.parsed (.num 0))) =
        some (.value 6 .both) ∧
      productValidationOf [1, 2, 3]
        (cells3 (.parsed (.num 2)) .presentEmpty (.parsed (.num 0)))
        (cells3 (.parsed (.num 3)) (.parsed (.num 5)) (.parsed (.num 0))) =
          some (.value 6 .growOnly) ∧
      productValidationOf [1, 2]
        (cells3 (.parsed (.num 2)) (.parsed (.num 4)) .empty)
        (cells3 (.parsed (.num 3)) (.parsed (.num 5)) .empty) =
          some (.value 26 .both) := by
  native_decide

/- The first unavailable reached cell owns suppression, with left-before-right order inside each pair. -/
example :
    productValidationOf [1]
      (cells3 (.rejected .declaredConstraint) .empty .empty)
      (cells3 (.rejected .malformed) .empty .empty) =
        some (.unknown .declaredConstraint) := by
  native_decide

/- Phase-sensitive reads share the fold: required-only emptiness suppresses validation but computes as zero, while ordinary formal invalidity poisons computation. -/
example :
    let zeros := cells3 (.parsed (.num 0)) (.parsed (.num 0)) (.parsed (.num 0))
    productCheckedValidationOf [1, 2, 3]
        (cells3 .presentEmpty (.parsed (.num 0)) (.parsed (.num 0)))
        (cells3 (.parsed (.num 5)) (.parsed (.num 0)) (.parsed (.num 0)))
        (requiredLeft := true) =
          some (.unknown .required) ∧
      productComputationOf [1, 2, 3]
        (cells3 .presentEmpty (.parsed (.num 0)) (.parsed (.num 0)))
        (cells3 (.parsed (.num 5)) (.parsed (.num 0)) (.parsed (.num 0)))
        (requiredLeft := true) =
          some (.value 0) ∧
      productComputationOf [1, 2, 3]
        (cells3 (.rejected .declaredConstraint) (.parsed (.num 0)) (.parsed (.num 0)))
        zeros = some (.poison .declaredConstraint) := by
  native_decide

/- Partial validation needs wildcard/ancestor extent coverage for both declarations; enumerating every current row or wildcarding only one field is insufficient. -/
example :
    let left := cells3 (.parsed (.num 2)) (.parsed (.num 4)) (.parsed (.num 0))
    let right := cells3 (.parsed (.num 3)) (.parsed (.num 5)) (.parsed (.num 0))
    let concreteAll := ValidationRelevanceScope.partialSet [
      productRelevance repeated.path [.concrete 1, .concrete 1, .concrete 1],
      productRelevance repeated.path [.concrete 1, .concrete 2, .concrete 1],
      productRelevance repeated.path [.concrete 1, .concrete 3, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .concrete 1, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .concrete 2, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .concrete 3, .concrete 1]]
    let leftOnly := ValidationRelevanceScope.partialSet [
      productRelevance repeated.path [.concrete 1, .all, .concrete 1]]
    let both := ValidationRelevanceScope.partialSet [
      productRelevance repeated.path [.concrete 1, .all, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .all, .concrete 1]]
    productPartialOf [1, 2, 3] left right concreteAll = some .nonRelevant ∧
      productPartialOf [1, 2, 3] left right leftOnly = some .nonRelevant ∧
      productPartialOf [1, 2, 3] left right both =
        some (.evaluated (.value 26 .fixed)) ∧
      productPartialOf [1, 2, 3] left right
        (.partialSet [productRelevance ["Form"] [.concrete 1]]) =
          some (.evaluated (.value 26 .fixed)) := by
  native_decide

/- Result scale is the exact sum of both field scales and never gains literal expansion capability. -/
example : productScale = some { scale := .exact 2, canExpandScale := false } := by
  native_decide

private def aggregateHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := absolute ["Form", "Rows"] "Amount" }
    { origin := .inner, field := absolute ["Form", "Rows"] "Amount" }

private def computationAggregateHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := absolute ["Form", "Rows"] "FilterLeft" }
    { origin := .inner, field := absolute ["Form", "Rows"] "FilterRight" }

private def aggregateSource (first : SurfaceNumberEntityOperand)
    (rest : List SurfaceNumberEntityOperand) : SurfaceNumberEntitySource :=
  { first, rest }

private def aggregateDocument (rows : List RowIndex) : Document :=
  { instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    rawCells := fun _ => none }

private def aggregateStarRead (a b c : RawCell)
    (environment : Env) (field : FieldId) : RawCell :=
  if field != repeated.id then .empty
  else match environment with
    | [(10, 1)] => a
    | [(10, 2)] => b
    | [(10, 3)] => c
    | _ => .empty

private def aggregateFilterRead (a b c : RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  repeated.checkRaw (aggregateStarRead a b c environment field)

private def aggregateComputationFilterRead
    (left right : RowIndex → RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  let row := match environment with
    | [(10, current)] => current
    | _ => 0
  if field == filterLeft.id then filterLeft.checkRaw (left row)
  else if field == filterRight.id then filterRight.checkRaw (right row)
  else malformedCheckedCell

private def aggregateComputationTargetRead (a b c : RawCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  repeated.checkRaw (aggregateStarRead a b c environment field)

private def checkedAggregateErrorOf (authored : SurfaceNumberEntitySource) :
    Option NumberEntityElabError :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .ok _ => none
  | .error error => some error

private def checkedAggregateOf (op : NumericAggregateOp)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext) : Option NumericOperand :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateAggregate op (aggregateDocument rows) [] direct
          (aggregateFilterRead a b c) (aggregateStarRead a b c) with
      | .ok result => some result
      | .error _ => none

private def checkedValueCountOf (expected : Rat)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext) : Option NumericOperand :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateValueCountValidationIn expected
          (aggregateDocument rows) [] (model.checkContext direct)
          (aggregateFilterRead a b c) with
      | .ok result => some result
      | .error _ => none

private def checkedComputationAggregateOf (op : NumericAggregateOp)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext)
    (leftFilter rightFilter : RowIndex → RawCell) :
    Option NumericComputationResult :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateComputation op (aggregateDocument rows) []
          (model.checkContext direct).read
          (aggregateComputationFilterRead leftFilter rightFilter)
          (aggregateComputationTargetRead a b c) with
      | .ok result => some result
      | .error _ => none

private def checkedComputationValueCountOf (expected : Rat)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext)
    (leftFilter rightFilter : RowIndex → RawCell) :
    Option NumericOperand :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluateValueCountComputation expected
          (aggregateDocument rows) [] (model.checkContext direct).read
          (aggregateComputationFilterRead leftFilter rightFilter)
          (aggregateComputationTargetRead a b c) with
      | .ok result => some result
      | .error _ => none

private def relevance (path : List String) (indices : List RelevanceIndex) :
    RelevantEntityPattern :=
  { path, indices }

private def checkedPartialAggregateOf (op : NumericAggregateOp)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext)
    (scope : ValidationRelevanceScope) :
    Option PartialValidationNumberAggregateResult :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartialAggregate op (aggregateDocument rows) [] scope
          direct (aggregateStarRead a b c) with
      | .ok result => some result
      | .error _ => none

private def checkedPartialValueCountOf (expected : Rat)
    (authored : SurfaceNumberEntitySource) (rows : List RowIndex)
    (a b c : RawCell) (direct : RawFlatContext)
    (scope : ValidationRelevanceScope) :
    Option PartialValidationNumberAggregateResult :=
  match elaborateNumberEntitySource model ["Form"] authored with
  | .error _ => none
  | .ok checked =>
      match checked.evaluatePartialValueCount expected
          (aggregateDocument rows) [] scope direct
          (aggregateStarRead a b c) with
      | .ok result => some result
      | .error _ => none

/- A partial instantiated prefix retains the model-owned omitted tail. -/
example : starSumOf (repeatedRaw [1] (.parsed (.num 8)) .empty .empty) =
    some (.value 8 .growOnly) := by
  native_decide

/- Exhausting the declared repetition removes the tail, while an explicit empty cell remains missing. -/
example :
    starSumOf (repeatedRaw [1, 2, 3] (.parsed (.num 8)) (.parsed (.num 9))
        (.parsed (.num 10))) = some (.value 27 .fixed) ∧
      starSumOf (repeatedRaw [1, 2, 3] (.parsed (.num 8)) .presentEmpty
        (.parsed (.num 10))) = some (.value 18 .growOnly) := by
  native_decide

/- A zero-row authored star is not the low-level fixed-empty state: all declared rows are an omitted tail. -/
example : starSumOf (repeatedRaw [] .empty .empty .empty) =
    some (.value 0 .both) := by
  native_decide

example :
    starExtremumOf .maximum
        (repeatedRaw [1] (.parsed (.num (-8))) .empty .empty) =
        some (.value (-8) .growOnly) ∧
      starExtremumOf .minimum
        (repeatedRaw [1] (.parsed (.num 8)) .empty .empty) =
        some (.value 8 .shrinkOnly) := by
  native_decide

example :
    starSumOf (repeatedRaw [1, 2, 3] (.parsed (.num tenPow50))
        (.parsed (.num (-tenPow50))) (.parsed (.num (3 / 5)))) =
      some (.value (3 / 5) .fixed) := by
  native_decide

example :
    starSumOf (repeatedRaw [1, 2] (.parsed (.num 8))
        (.rejected .declaredConstraint) .empty) =
      some (.unknown .declaredConstraint) := by
  native_decide

/- The checked aggregate accepts only a valid document prefix within the declared capacity. -/
example :
    starContextErrorOf (repeatedRaw [2] (.parsed (.num 8)) .empty .empty) =
        some (.noncontiguousCandidates [2]) ∧
      starContextErrorOf (repeatedRaw [1, 2, 3, 4] (.parsed (.num 8)) .empty .empty) =
        some (.exceedsRepeatability 4 3) := by
  native_decide

example :
    starElabErrorOf starredAmount
        ({ model with repeatableGroups := [{ rows with repeatability := none }] }) =
        some (.repeatabilityUnavailable rows.path) ∧
      starElabErrorOf starredAmount
        ({ model with repeatableGroups := [{ rows with repeatability := some 0 }] }) =
        some (.invalidRepeatability rows.path 0) := by
  native_decide

/- A selected first value makes a later omitted tail and invalid suffix invisible to both consumers. -/
example :
    starFirstFilledOf (repeatedRaw [1] (.parsed (.num 8)) .empty .empty) =
        some (.value 8 false) ∧
      starFirstFilledOf (repeatedRaw [1, 2, 3] (.parsed (.num 8))
        (.rejected .declaredConstraint) .presentEmpty) =
        some (.value 8 false) := by
  native_decide

/- An empty prefix is retained after selection in validation and erased by computation. -/
example :
    starFirstFilledOf (repeatedRaw [1, 2, 3] .presentEmpty
        (.parsed (.num 7)) (.rejected .declaredConstraint)) =
        some (.value 7 true) ∧
      (starFirstFilledOf (repeatedRaw [1, 2, 3] .presentEmpty
        (.parsed (.num 7)) (.rejected .declaredConstraint))).map
          FirstFilledNumberResult.asValidationOperand =
        some (.value 7 .both) ∧
      (starFirstFilledOf (repeatedRaw [1, 2, 3] .presentEmpty
        (.parsed (.num 7)) (.rejected .declaredConstraint))).map
          FirstFilledNumberResult.asComputationResult =
        some (.value 7) := by
  native_decide

/- A reached formal failure stops before a later value and keeps its exact cause in each phase. -/
example :
    starFirstFilledOf (repeatedRaw [1, 2] .presentEmpty
        (.rejected .declaredConstraint) .empty) =
        some (.unavailable .declaredConstraint) ∧
      (starFirstFilledOf (repeatedRaw [1, 2] .presentEmpty
        (.rejected .declaredConstraint) .empty)).map
          FirstFilledNumberResult.asValidationOperand =
        some (.unknown .declaredConstraint) ∧
      (starFirstFilledOf (repeatedRaw [1, 2] .presentEmpty
        (.rejected .declaredConstraint) .empty)).map
          FirstFilledNumberResult.asComputationResult =
        some (.poison .declaredConstraint) := by
  native_decide

/- No instantiated row reaches the model-owned omitted tail and therefore yields fillable zero only in validation. -/
example :
    starFirstFilledOf (repeatedRaw [] .empty .empty .empty) =
        some (.value 0 true) ∧
      (starFirstFilledOf (repeatedRaw [] .empty .empty .empty)).map
          FirstFilledNumberResult.asValidationOperand =
        some (.value 0 .both) ∧
      (starFirstFilledOf (repeatedRaw [] .empty .empty .empty)).map
          FirstFilledNumberResult.asComputationResult =
        some (.value 0) := by
  native_decide

/- The declared domain must be positive; a finite one-row star is still a valid checked source. -/
example :
    starElabErrorOf starredAmount
        ({ model with repeatableGroups := [{ rows with repeatability := some 1 }] }) =
      none := by
  native_decide

/- Authored field order reaches the existing staged precision-50 sum unchanged. -/
example :
    operandOf
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedC"])
        (raw (.parsed (.num tenPow50)) (.parsed (.num (-tenPow50)))
          (.parsed (.num (3 / 5)))) =
        some (.value (3 / 5) .fixed) ∧
      operandOf
        (sum (bare "SignedB") [bare "UnsignedC", bare "UnsignedA"])
        (raw (.parsed (.num tenPow50)) (.parsed (.num (-tenPow50)))
          (.parsed (.num (3 / 5)))) =
        some (.value 1 .fixed) := by
  native_decide

/- Missing direction comes from the missing declaration, not a representative present field. -/
example :
    operandOf (sum (bare "UnsignedA") [bare "SignedB"])
        (raw (.parsed (.num 7)) .presentEmpty .empty) =
        some (.value 7 .both) ∧
      operandOf (sum (bare "SignedB") [bare "UnsignedA"])
        (raw .presentEmpty (.parsed (.num 7)) .empty) =
        some (.value 7 .growOnly) := by
  native_decide

/- A source-level nonempty all-empty list has the aggregate's fillable zero identity. -/
example :
    operandOf (sum (bare "UnsignedA") [bare "SignedB"])
      (raw .empty .presentEmpty .empty) = some (.value 0 .both) := by
  native_decide

/- Raw input is classified with the same model and the first unavailable source wins. -/
example :
    operandOf
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedC"])
        (raw (.parsed (.num 7)) (.rejected .declaredConstraint)
          (.rejected .malformed)) =
      some (.unknown .declaredConstraint) := by
  native_decide

/- Wrong declared kinds and repeatable sources fail before a resolved side exists. -/
example :
    errorOf (sum (bare "Text") [bare "UnsignedA"]) =
        some (.fieldKindMismatch text.path .string) ∧
      errorOf (sum (absolute ["Form", "Rows"] "Amount") [bare "UnsignedA"]) =
        some (.resolve (.repeatableReference repeated.path)) := by
  native_decide

/- A singleton plain field is not a legal direct field-list aggregate; single starred/group operands belong to their expansion owners. -/
example : errorOf (sum (bare "UnsignedA") []) = some .tooFewFields := by
  native_decide

/- Duplicate rejection is global over declaration order rather than adjacent-only. -/
example :
    errorOf (sum (bare "UnsignedA") [bare "UnsignedA"]) =
        some (.duplicateField unsignedA.id) ∧
      errorOf
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedA"]) =
        some (.duplicateField unsignedA.id) := by
  native_decide

/- Duplicate detection precedes aggregate type checking, including when the repeated declaration has the wrong kind. -/
example : errorOf (sum (bare "Text") [bare "Text"]) =
    some (.duplicateField text.id) := by
  native_decide

/- Direct nonrepeatable extrema drop empty cells without substituting zero and retain their operator-specific missing direction. -/
example :
    extremumOperandOf .maximum
        (sum (bare "UnsignedA") [bare "SignedB"])
        (raw (.parsed (.num (-5))) .presentEmpty .empty) =
        some (.value (-5) .growOnly) ∧
      extremumOperandOf .minimum
        (sum (bare "UnsignedA") [bare "SignedB"])
        (raw (.parsed (.num 5)) .presentEmpty .empty) =
        some (.value 5 .shrinkOnly) := by
  native_decide

/- The shared checked field-list boundary preserves the extrema all-empty identity and first-unavailable cause. -/
example :
    extremumOperandOf .maximum
        (sum (bare "UnsignedA") [bare "SignedB"])
        (raw .empty .presentEmpty .empty) =
        some (.value 0 .both) ∧
      extremumOperandOf .minimum
        (sum (bare "UnsignedA") [bare "SignedB", bare "UnsignedC"])
        (raw (.parsed (.num 7)) (.rejected .declaredConstraint)
          (.rejected .malformed)) =
        some (.unknown .declaredConstraint) := by
  native_decide

/- Repeated plain and filtered wildcard slots are admitted, while a repeated direct field remains rejected even when a star separates its occurrences. -/
example :
    checkedAggregateErrorOf
        (aggregateSource (.star aggregateStar) [.star aggregateStar]) = none ∧
      checkedAggregateErrorOf
        (aggregateSource (.starHaving aggregateStar aggregateHaving)
          [.starHaving aggregateStar aggregateHaving]) = none ∧
      checkedAggregateErrorOf
        (aggregateSource (.star aggregateStar)
          [.starHaving aggregateStar aggregateHaving]) = none ∧
      checkedAggregateErrorOf
        (aggregateSource (.field (bare "UnsignedA")) [
          .star aggregateStar, .field (bare "UnsignedA")]) =
        some (.duplicateOperand unsignedA.id) := by
  native_decide

/- Every authored wildcard occurrence is expanded and consumed again; a reached filter retains its conservative polarity. -/
example :
    checkedAggregateOf .sum
        (aggregateSource (.star aggregateStar) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num 2)) (.parsed (.num 3))
        (.parsed (.num 0)) (raw .empty .empty .empty) =
      some (.value 10 .fixed) ∧
    checkedAggregateOf .sum
        (aggregateSource (.starHaving aggregateStar aggregateHaving)
          [.starHaving aggregateStar aggregateHaving])
        [1, 2, 3] (.parsed (.num 2)) (.parsed (.num 3))
        (.parsed (.num 0)) (raw .empty .empty .empty) =
      some (.value 10 .both) := by
  native_decide

/- Computation prefetches one kept successor before consuming the current aggregate target, so an invalid successor filter precedes an invalid current target. -/
example :
    checkedComputationAggregateOf .sum
        (aggregateSource
          (.starHaving aggregateStar computationAggregateHaving) [])
        [1, 2] (.rejected .declaredConstraint) (.parsed (.num 7)) .empty
        (raw .empty .empty .empty)
        (cells3 (.parsed (.num 1)) (.rejected .malformed) .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 1)) .empty) =
      some (.poison .malformed) := by
  native_decide

/- Once one successor is kept, an invalid current target terminates before any later filter is reached. -/
example :
    checkedComputationAggregateOf .sum
        (aggregateSource
          (.starHaving aggregateStar computationAggregateHaving) [])
        [1, 2, 3] (.rejected .declaredConstraint) (.parsed (.num 7))
        (.parsed (.num 9)) (raw .empty .empty .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) (.rejected .malformed))
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) (.parsed (.num 3))) =
      some (.poison .declaredConstraint) := by
  native_decide

/- A false row remains part of successor search, so poison after it still precedes the pending current target. -/
example :
    checkedComputationAggregateOf .sum
        (aggregateSource
          (.starHaving aggregateStar computationAggregateHaving) [])
        [1, 2, 3] (.rejected .declaredConstraint) (.parsed (.num 7))
        (.parsed (.num 9)) (raw .empty .empty .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) (.rejected .malformed))
        (cells3 (.parsed (.num 1)) (.parsed (.num 8)) (.parsed (.num 3))) =
      some (.poison .malformed) := by
  native_decide

/- Successful filtered computation retains ordinary aggregate accumulation rather than FirstFilledValue prefix termination. -/
example :
    checkedComputationAggregateOf .sum
        (aggregateSource
          (.starHaving aggregateStar computationAggregateHaving) [])
        [1, 2, 3] (.parsed (.num 2)) (.parsed (.num 3)) (.parsed (.num 100))
        (raw .empty .empty .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) (.parsed (.num 3)))
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) (.parsed (.num 9))) =
      some (.value 5) := by
  native_decide

/- The unfiltered branch uses the same computation-phase checked-cell projection and still combines direct and starred slots in authored order. -/
example :
    checkedComputationAggregateOf .sum
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [1, 2] (.parsed (.num 3)) (.parsed (.num 4)) .empty
        (raw (.parsed (.num 2)) .empty .empty)
        (cells3 .empty .empty .empty) (cells3 .empty .empty .empty) =
      some (.value 9) := by
  native_decide

/- A terminal direct operand remains stronger than later-slot filter lookahead. -/
example :
    checkedComputationAggregateOf .maximum
        (aggregateSource (.field (bare "UnsignedA")) [
          .starHaving aggregateStar computationAggregateHaving])
        [1, 2] (.parsed (.num 7)) (.parsed (.num 9)) .empty
        (raw (.rejected .declaredConstraint) .empty .empty)
        (cells3 (.rejected .malformed) (.parsed (.num 1)) .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 1)) .empty) =
      some (.poison .declaredConstraint) := by
  native_decide

/- Mixed direct/star slots retain authored encounter order across the existing staged precision-50 fold. -/
example :
    checkedAggregateOf .sum
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num (-tenPow50))) (.parsed (.num (3 / 5)))
        (.parsed (.num 0)) (raw (.parsed (.num tenPow50)) .empty .empty) =
      some (.value (3 / 5) .fixed) ∧
    checkedAggregateOf .sum
        (aggregateSource (.star aggregateStar) [.field (bare "UnsignedA")])
        [1, 2, 3] (.parsed (.num (-tenPow50))) (.parsed (.num (3 / 5)))
        (.parsed (.num 0)) (raw (.parsed (.num tenPow50)) .empty .empty) =
      some (.value 1 .fixed) := by
  native_decide

/- The same mixed checked route reaches both established extrema selectors without changing slot expansion. -/
example :
    checkedAggregateOf .minimum
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num (-2))) (.parsed (.num 3))
        (.parsed (.num 0)) (raw (.parsed (.num 4)) .empty .empty) =
      some (.value (-2) .fixed) ∧
    checkedAggregateOf .maximum
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num (-2))) (.parsed (.num 3))
        (.parsed (.num 0)) (raw (.parsed (.num 4)) .empty .empty) =
      some (.value 4 .fixed) := by
  native_decide

/- NumberOfDifferentValues consumes the same mixed checked stream but counts scale-normalized distinct filled values instead of folding every occurrence. -/
example :
    checkedAggregateOf .distinctCount
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num 5)) (.parsed (.num 6))
        (.parsed (.num 5)) (raw (.parsed (.num 5)) .empty .empty) =
      some (.value 2 .fixed) := by
  native_decide

/- Repeating a wildcard still consumes its values twice, but repeated equal occurrences do not inflate a value-distinct count. -/
example :
    checkedAggregateOf .distinctCount
        (aggregateSource (.star aggregateStar) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num 5)) (.parsed (.num 6))
        (.parsed (.num 5)) (raw .empty .empty .empty) =
      some (.value 2 .fixed) := by
  native_decide

/- Distinct count retains its own grow-only missing polarity and filter-driven both-directional uncertainty. -/
example :
    checkedAggregateOf .distinctCount
        (aggregateSource (.star aggregateStar) [])
        [] .empty .empty .empty (raw .empty .empty .empty) =
        some (.value 0 .growOnly) ∧
      checkedAggregateOf .distinctCount
        (aggregateSource (.star aggregateStar) [])
        [1, 2] (.parsed (.num 5)) .presentEmpty .empty
        (raw .empty .empty .empty) =
        some (.value 1 .growOnly) ∧
      checkedAggregateOf .distinctCount
        (aggregateSource (.starHaving aggregateStar aggregateHaving) [])
        [1, 2, 3] (.parsed (.num 5)) (.parsed (.num 5))
        (.parsed (.num 5)) (raw .empty .empty .empty) =
        some (.value 1 .both) := by
  native_decide

/- Numeric `NumberOfValueInFields` shares the checked entity-list expansion, but counts only filled scale-19-equal cells. -/
example :
    checkedValueCountOf 5
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [1, 2, 3] (.parsed (.num 5)) .presentEmpty
        (.parsed (.num 6)) (raw (.parsed (.num 5)) .empty .empty) =
      some (.value 2 .growOnly) := by
  native_decide

/- Filter provenance is retained per selected cell: a current match may disappear, while a selected non-match can only add a future match. -/
example :
    checkedValueCountOf 5
        (aggregateSource (.starHaving aggregateStar aggregateHaving) [])
        [1] (.parsed (.num 5)) .empty .empty
        (raw .empty .empty .empty) =
        some (.value 1 .both) ∧
      checkedValueCountOf 5
        (aggregateSource (.starHaving aggregateStar aggregateHaving) [])
        [1] (.parsed (.num 7)) .empty .empty
        (raw .empty .empty .empty) =
        some (.value 0 .growOnly) := by
  native_decide

/- Computation preserves the same selected-match distinction and the first reached formal cause. -/
example :
    checkedComputationValueCountOf 5
        (aggregateSource (.starHaving aggregateStar computationAggregateHaving) [])
        [1, 2] (.parsed (.num 5)) (.parsed (.num 7)) .empty
        (raw .empty .empty .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) .empty)
        (cells3 (.parsed (.num 1)) (.parsed (.num 2)) .empty) =
        some (.value 1 .both) ∧
      checkedComputationValueCountOf 5
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [2] (.parsed (.num 5)) .empty .empty
        (raw (.rejected .declaredConstraint) .empty .empty)
        (cells3 .empty .empty .empty) (cells3 .empty .empty .empty) =
        some (.unknown .declaredConstraint) := by
  native_decide

/- Partial validation reuses the aggregate all-rows gate and skips a locally visible filter before any reads. -/
example :
    let plain := aggregateSource (.star aggregateStar) []
    let filtered := aggregateSource
      (.starHaving aggregateStar aggregateHaving) []
    let wildcard := ValidationRelevanceScope.partialSet [
      relevance repeated.path [.concrete 1, .all, .concrete 1]]
    checkedPartialValueCountOf 5 plain [1, 2]
        (.parsed (.num 5)) (.parsed (.num 7)) .empty
        (raw .empty .empty .empty) wildcard =
        some (.evaluated (.value 1 .growOnly)) ∧
      checkedPartialValueCountOf 5 filtered [2]
        (.rejected .malformed) .empty .empty
        (raw .empty .empty .empty) (.partialSet []) =
        some .skippedHaving := by
  native_decide

/- A reached unavailable direct head determines the result before malformed later star topology is resolved. -/
example :
    checkedAggregateOf .maximum
        (aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar])
        [2] (.parsed (.num 9)) .empty .empty
        (raw (.rejected .declaredConstraint) .empty .empty) =
      some (.unknown .declaredConstraint) := by
  native_decide

/- Partial all-rows aggregates require wildcard or ancestor coverage; enumerating every current row concretely is insufficient. -/
example :
    let authored := aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar]
    let concreteAll := ValidationRelevanceScope.partialSet [
      relevance unsignedA.path [.concrete 1, .concrete 1],
      relevance repeated.path [.concrete 1, .concrete 1, .concrete 1],
      relevance repeated.path [.concrete 1, .concrete 2, .concrete 1],
      relevance repeated.path [.concrete 1, .concrete 3, .concrete 1]]
    let wildcard := ValidationRelevanceScope.partialSet [
      relevance unsignedA.path [.concrete 1, .concrete 1],
      relevance repeated.path [.concrete 1, .all, .concrete 1]]
    let ancestor := ValidationRelevanceScope.partialSet [
      relevance ["Form"] [.concrete 1]]
    checkedPartialAggregateOf .sum authored [1, 2, 3]
        (.parsed (.num 2)) (.parsed (.num 3)) (.parsed (.num 4))
        (raw (.parsed (.num 1)) .empty .empty) concreteAll =
      some .nonRelevant ∧
    checkedPartialAggregateOf .sum authored [1, 2, 3]
        (.parsed (.num 2)) (.parsed (.num 3)) (.parsed (.num 4))
        (raw (.parsed (.num 1)) .empty .empty) wildcard =
      some (.evaluated (.value 10 .fixed)) ∧
    checkedPartialAggregateOf .sum authored [1, 2, 3]
        (.parsed (.num 2)) (.parsed (.num 3)) (.parsed (.num 4))
        (raw (.parsed (.num 1)) .empty .empty) ancestor =
      some (.evaluated (.value 10 .fixed)) := by
  native_decide

/- NumberOfDifferentValues inherits the identical partial all-rows gate and evaluates only after wildcard/ancestor coverage. -/
example :
    let authored := aggregateSource (.star aggregateStar) []
    let concreteAll := ValidationRelevanceScope.partialSet [
      relevance repeated.path [.concrete 1, .concrete 1, .concrete 1],
      relevance repeated.path [.concrete 1, .concrete 2, .concrete 1],
      relevance repeated.path [.concrete 1, .concrete 3, .concrete 1]]
    let wildcard := ValidationRelevanceScope.partialSet [
      relevance repeated.path [.concrete 1, .all, .concrete 1]]
    checkedPartialAggregateOf .distinctCount authored [1, 2, 3]
        (.parsed (.num 5)) (.parsed (.num 6)) (.parsed (.num 5))
        (raw .empty .empty .empty) concreteAll =
      some .nonRelevant ∧
    checkedPartialAggregateOf .distinctCount authored [1, 2, 3]
        (.parsed (.num 5)) (.parsed (.num 6)) (.parsed (.num 5))
        (raw .empty .empty .empty) wildcard =
      some (.evaluated (.value 2 .fixed)) := by
  native_decide

/- A relevant unavailable prefix terminates before a later nonrelevant malformed star topology, while a nonrelevant direct prefix also masks that topology. -/
example :
    let authored := aggregateSource (.field (bare "UnsignedA")) [.star aggregateStar]
    let directOnly := ValidationRelevanceScope.partialSet [
      relevance unsignedA.path [.concrete 1, .concrete 1]]
    checkedPartialAggregateOf .maximum authored [2]
        (.parsed (.num 9)) .empty .empty
        (raw (.rejected .declaredConstraint) .empty .empty) directOnly =
      some (.evaluated (.unknown .declaredConstraint)) ∧
    checkedPartialAggregateOf .maximum authored [2]
        (.parsed (.num 9)) .empty .empty
        (raw (.parsed (.num 7)) .empty .empty) (.partialSet []) =
      some .nonRelevant := by
  native_decide

/- Any locally visible filtered slot skips the partial rule before direct classification or malformed star topology. -/
example :
    checkedPartialAggregateOf .minimum
        (aggregateSource (.field (bare "UnsignedA")) [
          .starHaving aggregateStar aggregateHaving])
        [2] (.rejected .malformed) .empty .empty
        (raw (.rejected .declaredConstraint) .empty .empty) (.partialSet []) =
      some .skippedHaving := by
  native_decide

end A12Kernel.Conformance.NumericAggregateElaboration
